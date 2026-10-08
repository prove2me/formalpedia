-- Prove2me | Theorems.Thm_TopkisRation_Myopic_C_convex_continuous
-- name    : TopkisRation.Myopic.C_convex_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:37.417825+00:00
-- url     : https://prove2.me/theorems/dd68dc50-3475-4ccf-99a0-b87072195bb9
-- title:
--   §3, pp. 174–175 — continuation and ordering costs are convex and continuous
-- statement:
--   Under the standing assumptions of the multiperiod model, every continuation value $C_m$, for $1\le m\le N+1$, is convex and continuous as a real function of net stock. In each actual ordering period, $1\le m\le N$, the pre-order cost $\widetilde g^{,m}$ is convex and continuous on nonnegative order-up-to levels:
--
--   $$C_m\text{ is convex and continuous on }\mathbb R,\qquad \widetilde g^{,m}\text{ is convex and continuous on }[0,\infty).$$
--
--   This regularity makes the ordering minimization in equation (19) meaningful and supports the critical-level policy.
--
--   **Formalization Note** The page also recalls the §1 characterization of optimal rationing. That separate result is Theorem 1 of this paper and is outside this statement.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), pp. 174–175, §3, The General Case, paragraph after (19)

import Definitions.Def_TopkisRation_Myopic_MultiPeriod

namespace TopkisRation.Myopic

variable {n : ℕ}

/-- The General Case, pp. 174–175: the continuation and ordering cost functions are convex and continuous. -/
theorem C_convex_continuous (Q : MultiModel n) (hQ : Q.Standing) :
    (∀ m ∈ Finset.Icc 1 (Q.N + 1),
      ConvexOn ℝ Set.univ (Q.C m) ∧ Continuous (Q.C m)) ∧
    (∀ m ∈ Finset.Icc 1 Q.N,
      ConvexOn ℝ (Set.Ici 0) (Q.gtilde m) ∧ ContinuousOn (Q.gtilde m) (Set.Ici 0)) := by sorry

end TopkisRation.Myopic
