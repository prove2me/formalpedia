-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_corollary_6_8
-- name    : QMatVecLB.ConvexOpt.corollary_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:17:38.263814+00:00
-- url     : https://prove2.me/theorems/29b4fb43-04d6-4989-ae20-8cf712a95a5f
-- title:
--   Corollary 6.8 — positive-definite inverse-column lower bound
-- statement:
--   For all sufficiently large $n$, consider symmetric real matrices with the Loewner bounds
--
--   $$n^{-13}I\preceq M\preceq9nI.$$
--
--   Every matrix-vector phase-query algorithm which, for every such $M$, returns $w$ satisfying
--
--   $$\|w-M^{-1}e_1\|_2\le\tfrac16 n^{-7/2}$$
--
--   with probability at least $2/3$, requires $t\ge c n/\log n$ for an absolute $c>0$. The algorithm may choose every finite discretization level and finite workspace independently of $M$. The promise implies positive definiteness. This is the precise quantitative version of positive-definite inversion in the corollary.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
--   - encoding: finite-register t-query quantum algorithms and general final measurements → normalized finite-dimensional complex states, t+1 input-independent unitary gates, exact diagonal phase queries tensored with an arbitrary finite workspace, and basis readout with an output map; reason: this is the circuit model of Section 3.1; arbitrary finite outcome measurements are represented by unitary dilation into the unrestricted workspace
--   - encoding: Omega(n/log n) bounded-error quantum query complexity → there exist c>0 and N>=2, uniformly over all n>=N, k>=1, finite workspaces and circuits, such that worst-case success >=2/3 implies t>=c*n/log n; reason: this expands the asymptotic and bounded-error conventions of Section 2 and the proof of Corollary 6.8; increasing an eventual threshold to 2 loses no instances
--   - reading: the general first-column task and the precise In particular sentence → the full inverse-column approximation task and Loewner promise of the second sentence; reason: that sentence fixes the accuracy left unspecified in the first sentence
--   - encoding: Loewner bounds and Euclidean first-column error → explicit symmetry and two positive-semidefinite differences; the first column as a EuclideanSpace vector; reason: these are equivalent definitions of the stated promise and norm; no separate positive-definiteness assumption is added
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Corollary 6.8, PDF p. 26 (printed p. 25).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Inversion

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem corollary_6_8 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ k : ℕ, 1 ≤ k → ∀ (W : Type) [Fintype W] (t : ℕ)
        (alg : QueryAlg (MatQuery n k) W (RVec n) t),
      (∀ M : RMat n, positivePromise M →
        (2/3 : ℝ) ≤ alg.prob (matPhase M)
          (fun w => ‖w - firstColumnN M‖ ≤ (1/6 : ℝ) * Real.rpow (n : ℝ) (-(7/2 : ℝ)))) →
      c * (n : ℝ) / Real.log n ≤ (t : ℝ) := by sorry

end QMatVecLB.ConvexOpt
