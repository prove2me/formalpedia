-- Prove2me | Theorems.Thm_StochSQP_Vanishing_Supplement_theorem_1
-- name    : StochSQP.Vanishing.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:22:11.24383+00:00
-- url     : https://prove2.me/theorems/c6149a58-bd16-484a-9968-863a117bbf05
-- title:
--   Theorem 1 (companion theorem; not used in the proof of the goal) — complete deterministic convergence
-- statement:
--   Consider Algorithm 1 under Assumptions 1 and 3, exact gradients, and constant $\beta$ satisfying (23). Let $Z_k$ be any orthonormal null-space basis. If the Jacobians eventually have a uniform positive lower bound on all row singular values, the merit sequence has a positive uniform lower bound and
--   $$\lim_{k\to\infty}\left\|\begin{bmatrix}\nabla f(x_k)+J_k^Ty_k\\c_k\end{bmatrix}\right\|_2=\lim_{k\to\infty}\left\|\begin{bmatrix}Z_k^T\nabla f(x_k)\\c_k\end{bmatrix}\right\|_2=0.$$
--   Otherwise,
--   $$\lim_{k\to\infty}\|J_k^Tc_k\|_2=0,$$
--   and a positive uniform lower bound on $\tau_k$ additionally implies
--   $$\lim_{k\to\infty}\|\nabla f(x_k)+J_k^Ty_k\|_2=\lim_{k\to\infty}\|Z_k^T\nabla f(x_k)\|_2=0.$$
--   This companion theorem retains every clause of (24)–(26) and the full domain $m\le n$. It is separate from the published stochastic vanishing-merit goal.
--
--   Differences from the source:
--   - encoding: Euclidean matrix notation and sequence limits → finite Euclidean spaces, adjoints, varying-dimensional isometries, and Tendsto to zero; reason: these express the same vectors, norms, bases and full-sequence limits, including zero-dimensional spaces
--   - encoding: the infinite-run convention on p. 11 and the optional stationary stop in Appendix A → the published IsRun predicate with feasible stationary zero steps allowed; reason: finite infeasible-stationary returns already have the source certificate; extending a feasible stationary return by zero steps preserves all claimed limits, without adding a nonstationarity premise
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 10, Theorem 1; Appendix A, pp. 29–31

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Supplement_Geometry
import Definitions.Def_StochSQP_Vanishing_Supplement_Deterministic

namespace StochSQP.Vanishing.Supplement

open Filter
open scoped InnerProductSpace RealInnerProductSpace Topology

theorem theorem_1
    {n m : ℕ} (P : Problem n m) (A : Params) (R : Run n m)
    (X : Set (E n)) (κH ζH : ℝ)
    (hA : A.Valid) (hP : Assumption1 P A.L A.Γ X)
    (hx : ∀ k, R.x k ∈ X) (hH : Assumption3 P R κH ζH)
    (hrun : IsRun P A R)
    (hdet : Deterministic P A R) (B : NullBases P R) :
    (EventualFullRank P R →
      PositiveMerit R ∧
      Tendsto (fun k => blockNorm (lagrangianNorm P R k) ‖P.c (R.x k)‖) atTop (nhds 0) ∧
      Tendsto (fun k => blockNorm (reducedNorm P R B k) ‖P.c (R.x k)‖) atTop (nhds 0)) ∧
    (¬ EventualFullRank P R →
      Tendsto (fun k => ‖P.Jt (R.x k) (P.c (R.x k))‖) atTop (nhds 0) ∧
      (PositiveMerit R →
        Tendsto (lagrangianNorm P R) atTop (nhds 0) ∧
        Tendsto (reducedNorm P R B) atTop (nhds 0))) := by sorry

end StochSQP.Vanishing.Supplement
