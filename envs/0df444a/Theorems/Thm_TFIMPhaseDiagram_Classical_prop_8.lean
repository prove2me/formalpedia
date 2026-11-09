-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_prop_8
-- name    : TFIMPhaseDiagram.Classical.prop_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:50.199204+00:00
-- url     : https://prove2.me/theorems/59563754-5c1c-474c-908f-2e1e6f2a2a1e
-- title:
--   Proposition 8 — Exact quantum/classical trace identities (8) and (9)
-- statement:
--   Let $J$ be symmetric, $h$ real, and every $\eta_i\ge0$. For a Pauli string $O=\prod_iP_i$, set $S=\{i:P_i\in\{X,Y\}\}$, $q=|\{i:P_i=Y\}|$, $C=\operatorname{Tr}(X_Se^{H_x})$, and $D=\operatorname{Tr}(X_S(e^{\sum_i h_i Z_i/M}e^{H_x/M})^M)$. Both $C,D$ are real and nonnegative. With the path and tilted-cycle laws of (7),
--   $$\operatorname{Tr}(Oe^H)=i^qC\,\mathbb E_\nu[e^Vf],\qquad\operatorname{Tr}(OQ_M)=i^qC\,\mathbb E_\nu[e^{V^{(M)}}f]=i^qD\,\mathbb E_{\widetilde\nu}[e^Wf].$$
--   These are both exact trace identities (8) and (9), including arbitrary $Y$ factors and zero fields. They identify the classical quantities used in every estimator.
--
--   Differences from the source:
--   - encoding: Pauli tensors and path expectations (8),(9) → bitstring matrices, jump data, complex trace equalities and real nonnegative constants; reason: The same matrices and probability laws are used; zero transverse fields remain included.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.7 = PDF p.7, Proposition 8

import Definitions.Def_TFIMPhaseDiagram_Classical_traceSetup

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Proposition 8, p.7, both (8) and (9); the section assumes eta_i >= 0. -/
theorem prop_8 {n : ℕ} (hn : 0 < n) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.IsSymm) (h η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i)
    (P : Fin n → Pauli) (M : ℕ) (hM : 3 ≤ M) :
  let C := Matrix.trace (xSubset (flipSet P) * matrixExp (hx η))
  let D := Matrix.trace (xSubset (flipSet P) * trotter 0 h η M)
  C.im = 0 ∧ 0 ≤ C.re ∧ D.im = 0 ∧ 0 ≤ D.re ∧
  Matrix.trace (pauliString P * matrixExp (hamiltonian J h η)) =
    Complex.I ^ yCount P * C * (∫ σ, Real.exp (pathPotential J h σ) * pathSign P σ ∂nu η P : ℝ) ∧
  Matrix.trace (pauliString P * trotter J h η M) =
    Complex.I ^ yCount P * C * (∫ σ, Real.exp (meshPotential J h M σ) * pathSign P σ ∂nu η P : ℝ) ∧
  Matrix.trace (pauliString P * trotter J h η M) =
    Complex.I ^ yCount P * D * (∫ s, Real.exp (cycleInteraction J s) * meshSign P s ∂nuTilde (M := M) h η P : ℝ) := by sorry
end TFIMPhaseDiagram.Classical
