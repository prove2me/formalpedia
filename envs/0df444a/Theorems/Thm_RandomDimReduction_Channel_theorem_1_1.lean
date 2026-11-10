-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_theorem_1_1
-- name    : RandomDimReduction.Channel.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:26:22.350449+00:00
-- url     : https://prove2.me/theorems/377e6dbd-9b3a-41a9-ab29-dad30fcbcc49
-- title:
--   Theorem 1.1 — efficient random dimension reduction
-- statement:
--   There are constants $c>0$ and $K\in\mathbb N$, independent of every instance. For every positive $n,k,d$ with $k\le d$, the map $R^{\rm TP}$ defined by Eq.(3) is complex-linear, completely positive and trace preserving. For every isometry $W:\mathbb C^k\to\mathbb C^d$ and every complex operator $X_0$ on $(\mathbb C^k)^{\otimes n}$,
--   $$ R^{\rm TP}\bigl(W^{\otimes n}X_0(W^{\otimes n})^\dagger\bigr)
--   =\mathbb E_{U\sim U(k)}[U^{\otimes n}X_0(U^{\otimes n})^\dagger]. $$
--   For every $0<\varepsilon<1$, there is a qubit circuit $C$ such that
--   $$ |C|\le c(n+\log d+\log(1/\varepsilon)+2)^K,\qquad
--   \|\Phi_C\circ\mathrm{Enc}_{d,n}-\mathrm{Enc}_{k,n}\circ R^{\rm TP}\|_\diamond\le\varepsilon. $$
--   The approximation concerns the entire channel, with entangled reference inputs and no support promise. The circuit family is not required to be uniform. All three source conclusions are retained.
--
--   Differences from the source:
--   - encoding: finite-dimensional tensor Hilbert spaces and complex linear operators → matrices on Fin n → Fin d, with zero-based coordinates; reason: standard orthonormal coordinates preserve every operator and isometry
--   - encoding: the Moore–Penrose inverse followed by its positive square root → real spectral functional calculus x ↦ (sqrt x)⁻¹, with zero at zero; reason: the Grassmannian moment is positive semidefinite; its finite spectrum includes zero and needs no invertibility hypothesis
--   - encoding: R^TP is a quantum channel → there exists a complex-linear map agreeing with Eq.(3) on every input and satisfying the published CPTP predicate; reason: the agreement witness expresses linearity as a conclusion without assuming channel validity
--   - encoding: poly(n, log d, log(1/ε)) elementary gates to ε accuracy → global c > 0 and natural K bound gates plus wires by c(n + log d + log(1/ε) + 2)^K, for 0 < ε < 1; reason: a single multivariate polynomial is bounded by this expression; logarithm bases only rescale constants, and idle ancillas can be omitted
--   - reading: elementary gates and diamond-norm implementation → unitary one- and two-qubit gates with zero ancillas and discarded outputs, in the unhalved diamond norm; reason: this fixes the elementary-gate convention and the stronger of the two diamond-distance normalizations
--   - encoding: operators on qudits or Schur registers implemented by a circuit → fixed binary encodings of basis indices, with a reference of the original input dimension; reason: basis isometries preserve the whole-map diamond comparison; the encodings are fixed before ε and dimension one uses zero qubits
--   - encoding: an operator X with hypothesis X = W tensor X₀ tensor W† → the embedded expression is substituted directly for X; reason: substitution preserves every instance of the source equality hypothesis
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Theorem 1.1, p.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Moment
import Definitions.Def_RandomDimReduction_Channel_Circuits

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 1.1, p.2, at full strength: CPTP validity, Eq.(1) for every
isometry and arbitrary complex X₀, and an honest whole-channel circuit bound. -/
theorem theorem_1_1 :
    ∃ (c : ℝ) (K : ℕ), 0 < c ∧
      ∀ n k d : ℕ, 0 < n → 1 ≤ k → k ≤ d →
      (∃ L : Op (Word n d) →ₗ[ℂ] Op (Word n k),
        (∀ X, L X = RTP n k d X) ∧ WildeQIT.EntBreaking.IsQuantumChannel L) ∧
      (∀ (W : Matrix (Fin d) (Fin k) ℂ), Wᴴ * W = 1 → ∀ X₀ : Op (Word n k),
        RTP n k d (tensor n W * X₀ * (tensor n W)ᴴ) = twirl n k X₀) ∧
      (∀ eps : ℝ, 0 < eps → eps < 1 →
        ∃ C : Circuit (inputQubits n d) (inputQubits n k),
          (circuitSize C : ℝ) ≤ polyBound c K n d eps ∧
          diamond (fun X : Op (Word n d) =>
            circuitChannel C (encode n d X) - encode n k (RTP n k d X)) ≤
              ENNReal.ofReal eps) := by sorry

end RandomDimReduction.Channel
