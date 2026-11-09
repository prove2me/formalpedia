-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_theorem_6_6
-- name    : QMatVecLB.ConvexOpt.theorem_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:17:12.150585+00:00
-- url     : https://prove2.me/theorems/3e7404d4-29b0-46bb-b061-83b878613f4d
-- title:
--   Theorem 6.6 — inverse-entry decision lower bound (precise sentence)
-- statement:
--   Fix $\theta\ge5$. For all sufficiently large $n$, consider real $(n+1)\times(n+1)$ matrices satisfying
--
--   $$\sigma_{\min}(A)\ge n^{-13/2},\quad\sigma_{\max}(A)\le3\sqrt n,\quad |(A^{-1})_{11}|\le\theta-n^{-3}\ \text{or}\ |(A^{-1})_{11}|\ge\theta+n^{-3}.$$
--
--   Every bounded-error quantum algorithm distinguishing the two cases using matrix-vector phase queries requires
--
--   $$t\ge c_\theta\,n/\log n$$
--
--   for a positive constant depending only on $\theta$. The statement covers every freely chosen finite discretization level and finite workspace, with the circuit fixed before the input matrix. This is the precise inverse-entry task in the theorem's second sentence.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
--   - encoding: finite-register t-query quantum algorithms and general final measurements → normalized finite-dimensional complex states, t+1 input-independent unitary gates, exact diagonal phase queries tensored with an arbitrary finite workspace, and basis readout with an output map; reason: this is the circuit model of Section 3.1; arbitrary finite outcome measurements are represented by unitary dilation into the unrestricted workspace
--   - encoding: Omega(n/log n) bounded-error quantum query complexity → there exist c>0 and N>=2, uniformly over all n>=N, k>=1, finite workspaces and circuits, such that worst-case success >=2/3 implies t>=c*n/log n; reason: this expands the asymptotic and bounded-error conventions of Section 2 and the proof of Corollary 6.8; increasing an eventual threshold to 2 loses no instances
--   - reading: computing the first inverse column, followed by an explicit decision task → the full explicit decision task in the In particular sentence; reason: the first sentence specifies no approximation accuracy; the second gives the precise promise and task proved and used downstream
--   - encoding: paper inverse entry (1,1) → Lean entry (0,0); reason: Fin indices start at zero; all singular-value promises are unchanged
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Theorem 6.6, PDF p. 23 (printed p. 22).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Inversion

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem theorem_6_6 (θ : ℝ) (hθ : 5 ≤ θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ k : ℕ, 1 ≤ k → ∀ (W : Type) [Fintype W] (t : ℕ)
        (alg : QueryAlg (MatQuery (n+1) k) W Bool t),
      (∀ A : RMat (n+1),
        Real.rpow (n : ℝ) (-(13/2 : ℝ)) ≤ GaussianMatrix.sMin A →
        GaussianMatrix.specNorm A ≤ 3 * Real.sqrt n →
        (|A⁻¹ 0 0| ≤ θ - 1 / (n : ℝ)^3 ∨ θ + 1 / (n : ℝ)^3 ≤ |A⁻¹ 0 0|) →
        (2/3 : ℝ) ≤ alg.prob (matPhase A)
          (fun b => b = decide (θ + 1 / (n : ℝ)^3 ≤ |A⁻¹ 0 0|))) →
      c * (n : ℝ) / Real.log n ≤ (t : ℝ) := by sorry

end QMatVecLB.ConvexOpt
