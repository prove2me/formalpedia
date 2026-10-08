-- Prove2me | Theorems.Thm_QualityEncroach_FixedCost_lemma_2
-- name    : QualityEncroach.FixedCost.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:55.142496+00:00
-- url     : https://prove2.me/theorems/d655408f-9802-450c-8145-86132bd5b6b6
-- title:
--   Lemma 2, p. 36 — low direct quality is not optimal with encroachment
-- statement:
--   Let $k>0$ and $c\ge0$. Maximize the low-direct-quality reduced profit from equation (22) over pairs $(t,u)$ with $t\ge1$ and $(8t-3)c<(6t-3)u$. If $(t,u)$ is a maximizer on this strict encroachment-feasible set, then
--
--   $$t=1.$$
--
--   This is the positive-direct-sales part of Lemma 2; its other alternative, no encroachment, lies on the excluded boundary. Together with Claim 3 it supports Proposition 6(i).
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, pp. 36–37, Lemma 2 and equation (22)

import Mathlib
import Definitions.Def_QualityEncroach_FixedCost_Reduced

namespace QualityEncroach.FixedCost

/-- Lemma 2, p. 36: an optimal encroaching solution in the `1 ≤ t` branch
cannot have `t > 1`. The no-encroachment alternative lies on the excluded
boundary `(6t-3)u = (8t-3)c`. -/
theorem lemma_2 (k c t u : ℝ) (hk : 0 < k) (hc : 0 ≤ c)
    (ht : 1 ≤ t) (hu : (8 * t - 3) * c < (6 * t - 3) * u)
    (hopt : ∀ t' u' : ℝ, 1 ≤ t' →
      (8 * t' - 3) * c < (6 * t' - 3) * u' →
      PiLo k c t' u' ≤ PiLo k c t u) :
    t = 1 := by sorry

end QualityEncroach.FixedCost
