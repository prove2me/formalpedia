-- Prove2me | Theorems.Thm_StochSQP_Vanishing_Supplement_lemma_18
-- name    : StochSQP.Vanishing.Supplement.lemma_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:18:51.878162+00:00
-- url     : https://prove2.me/theorems/a5df57a9-5fc7-490c-9f12-8eaf21e915d1
-- title:
--   Lemma 18 (used in the proof of Theorem 1) — deterministic merit decrease
-- statement:
--   In the deterministic context of Appendix A, with Assumptions 1 and 3, exact gradients and constant $\beta$ satisfying (23), every iteration satisfies
--   $$\phi(x_k,\tau_k)-\phi(x_k+\alpha_kd_k,\tau_k)\ge\eta\alpha_k\Delta l(x_k,\tau_k,g_k,d_k).$$
--   Here $\phi(x,\tau)=\tau f(x)+\|c(x)\|_2$ and $\Delta l$ is the model reduction (13). This is sufficient decrease for the actual step selected by Algorithm 1.
--
--   Differences from the source:
--   - encoding: Euclidean matrix notation and sequence limits → finite Euclidean spaces, adjoints, varying-dimensional isometries, and Tendsto to zero; reason: these express the same vectors, norms, bases and full-sequence limits, including zero-dimensional spaces
--   - encoding: the infinite-run convention on p. 11 and the optional stationary stop in Appendix A → the published IsRun predicate with feasible stationary zero steps allowed; reason: finite infeasible-stationary returns already have the source certificate; extending a feasible stationary return by zero steps preserves all claimed limits, without adding a nonstationarity premise
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 30, Lemma 18; Appendix A, pp. 29–31

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Supplement_Geometry
import Definitions.Def_StochSQP_Vanishing_Supplement_Deterministic

namespace StochSQP.Vanishing.Supplement

open Filter
open scoped InnerProductSpace RealInnerProductSpace Topology

theorem lemma_18
    {n m : ℕ} (P : Problem n m) (A : Params) (R : Run n m)
    (X : Set (E n)) (κH ζH : ℝ)
    (hA : A.Valid) (hP : Assumption1 P A.L A.Γ X)
    (hx : ∀ k, R.x k ∈ X) (hH : Assumption3 P R κH ζH)
    (hrun : IsRun P A R)
    (hdet : Deterministic P A R) : ∀ k : ℕ,
    merit P (R.x k) (R.τ k) - merit P (R.x k + R.α k • R.d k) (R.τ k) ≥
      A.η * R.α k * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by sorry

end StochSQP.Vanishing.Supplement
