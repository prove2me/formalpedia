-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_lemma_6_7
-- name    : QMatVecLB.ConvexOpt.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:08:46.99027+00:00
-- url     : https://prove2.me/theorems/32b09b2a-70a1-4863-a84e-8136ec2b24b0
-- title:
--   Lemma 6.7 — one-query products and three-query simulation
-- statement:
--   Let $n\ge1$, $\Lambda\ge1$, $L\ge1$, $0<\epsilon<1$, and
--
--   $$k\ge\log_2(256n^3\Lambda L/\epsilon^3).$$
--
--   For every grid vector $x$ with $\|x\|_\infty\le L$ and either choice of transpose, there is a one-query circuit, independent of $A$, that estimates $Ax$ or $A^Tx$ with sup-norm error at most $\epsilon$ and probability at least $1-\epsilon$, for every matrix with $\|A\|_{\max}\le\Lambda$.
--
--   There is also a three-query circuit and a fixed unit ancilla, both independent of $A$, whose output has pure-state trace distance at most $\epsilon$ from $(\widehat U_{AA^T}\phi)\otimes\omega$ for every admissible $A$ and every unit query state $\phi$ supported on grid pairs with both sup norms at most $L$. The input is $\phi\otimes\omega$. These guarantees specify uniform query simulation rather than a circuit chosen for each input matrix.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
--   - encoding: finite-register t-query quantum algorithms and general final measurements → normalized finite-dimensional complex states, t+1 input-independent unitary gates, exact diagonal phase queries tensored with an arbitrary finite workspace, and basis readout with an output map; reason: this is the circuit model of Section 3.1; arbitrary finite outcome measurements are represented by unitary dilation into the unrestricted workspace
--   - encoding: Lambda >= max{max-norm A,1}, for matrix-independent unitaries → Lambda >= 1, then a circuit exists before all A with maxNorm A <= Lambda; reason: this exposes the uniformity in the source instead of permitting input-dependent hard-coding
--   - reading: implementation within trace distance epsilon on the indicated query registers → a bound for all supported coherent unit vectors, with a fixed returned ancilla and pure-state distance sqrt(1-|inner|^2); reason: the proof states that the implementation is a direct sum over x,y; this is the coherent reading required by the hybrid reductions
--   - encoding: positive matrix dimension and log base two → 1 <= n and Real.log(argument)/Real.log 2; reason: the precision condition is the identical logarithmic threshold, on its positive domain
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 6.7, PDF p. 25 (printed p. 24).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_GridOracle

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem lemma_6_7 (n : ℕ) (hn : 1 ≤ n) (Λ L ε : ℝ)
    (hΛ : 1 ≤ Λ) (hL : 1 ≤ L) (hε : 0 < ε) (hε1 : ε < 1)
    (k : ℕ)
    (hprecision : Real.log (256 * (n : ℝ)^3 * Λ * L / ε^3) / Real.log 2 ≤ (k : ℝ)) :
    (∀ x : GridVec n k, supNorm (fun i => gridValue (x i)) ≤ L →
      ∀ transpose : Bool, ∃ (w : ℕ) (alg : QueryAlg (MatQuery n k) (Fin w) (Fin n → ℝ) 1),
        ∀ A : RMat n, maxNorm A ≤ Λ →
          1 - ε ≤ alg.prob (matPhase A) (fun z =>
            supNorm (z - (if transpose then A.transpose else A) *ᵥ (fun i => gridValue (x i))) ≤ ε)) ∧
    (∃ (w : ℕ) (ω : Ket (Fin w)) (C : QueryCircuit (MatQuery n k) (Fin w) 3),
      ‖ω‖ = 1 ∧ ∀ A : RMat n, maxNorm A ≤ Λ →
        ∀ φ : Ket (MatQuery n k), ‖φ‖ = 1 →
          (∀ xy : MatQuery n k,
            (L < supNorm (fun i => gridValue (xy.1 i)) ∨
             L < supNorm (fun i => gridValue (xy.2 i))) → φ xy = 0) →
          pureDistance (C.evolve (matPhase A) (tensorKet φ ω))
            (tensorKet (WithLp.toLp 2 (fun xy => matPhase (A * A.transpose) xy * φ xy)) ω) ≤ ε) := by sorry

end QMatVecLB.ConvexOpt
