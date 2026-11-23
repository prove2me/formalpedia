-- Prove2me | Theorems.Thm_StochSQP_Vanishing_Supplement_lemma_20
-- name    : StochSQP.Vanishing.Supplement.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:20:52.145537+00:00
-- url     : https://prove2.me/theorems/848ae1e7-f09b-49ea-aec8-59c82d33f145
-- title:
--   Lemma 20 (used in the proof of Theorem 1) — complete feasibility-stationarity limit
-- statement:
--   Under the deterministic context of Appendix A,
--   $$\lim_{k\to\infty}\|J_k^Tc_k\|_2=0.$$
--   Moreover, if all row singular values of $J_k$ are uniformly bounded below by a positive constant after some index, then
--   $$\lim_{k\to\infty}\|c_k\|_2=0.$$
--   Both assertions concern the full sequence. They distinguish feasibility from stationarity of constraint violation.
--
--   Differences from the source:
--   - encoding: Euclidean matrix notation and sequence limits → finite Euclidean spaces, adjoints, varying-dimensional isometries, and Tendsto to zero; reason: these express the same vectors, norms, bases and full-sequence limits, including zero-dimensional spaces
--   - encoding: the infinite-run convention on p. 11 and the optional stationary stop in Appendix A → the published IsRun predicate with feasible stationary zero steps allowed; reason: finite infeasible-stationary returns already have the source certificate; extending a feasible stationary return by zero steps preserves all claimed limits, without adding a nonstationarity premise
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 31, Lemma 20; Appendix A, pp. 29–31

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Supplement_Geometry
import Definitions.Def_StochSQP_Vanishing_Supplement_Deterministic

namespace StochSQP.Vanishing.Supplement

open Filter
open scoped InnerProductSpace RealInnerProductSpace Topology

theorem lemma_20
    {n m : ℕ} (P : Problem n m) (A : Params) (R : Run n m)
    (X : Set (E n)) (κH ζH : ℝ)
    (hA : A.Valid) (hP : Assumption1 P A.L A.Γ X)
    (hx : ∀ k, R.x k ∈ X) (hH : Assumption3 P R κH ζH)
    (hrun : IsRun P A R)
    (hdet : Deterministic P A R) :
    Tendsto (fun k => ‖P.Jt (R.x k) (P.c (R.x k))‖) atTop (nhds 0) ∧
    (EventualFullRank P R → Tendsto (fun k => ‖P.c (R.x k)‖) atTop (nhds 0)) := by sorry

end StochSQP.Vanishing.Supplement
