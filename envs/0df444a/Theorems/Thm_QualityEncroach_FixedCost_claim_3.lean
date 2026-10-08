-- Prove2me | Theorems.Thm_QualityEncroach_FixedCost_claim_3
-- name    : QualityEncroach.FixedCost.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:07.489068+00:00
-- url     : https://prove2.me/theorems/89c89fad-f639-44ec-b737-18b9af496bc8
-- title:
--   Claim 3, p. 36 — no differentiation in the high-direct-quality branch
-- statement:
--   Let $k>0$ and $c>0$. Maximize the high-direct-quality reduced profit over pairs $(t,u)$ with $0<t\le1$ and $u>(8-3t)c/(8-5t)$. Every maximizer $(t,u)$ satisfies
--
--   $$t=1.$$
--
--   This is the high-direct-quality half of Proposition 6(i).
--
--   **Formalization Note** The maximization is joint in $(t,u)$ and uses the strict positive-direct-sales domain. The added $c>0$ is necessary: at $c=0$ this reduced profit is independent of $t$.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 36, Claim 3 and its proof

import Mathlib
import Definitions.Def_QualityEncroach_FixedCost_Reduced

namespace QualityEncroach.FixedCost

/-- Claim 3, p. 36, read as a joint maximization over the open
encroachment-feasible set. The page's fixed-`u` derivative argument does not
assert that `t = 1` is feasible for that fixed `u`. -/
theorem claim_3 (k c t u : ℝ) (hk : 0 < k) (hc : 0 < c)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hu : (8 - 3 * t) * c / (8 - 5 * t) < u)
    (hopt : ∀ t' u' : ℝ, 0 < t' → t' ≤ 1 →
      (8 - 3 * t') * c / (8 - 5 * t') < u' →
      PiHi k c t' u' ≤ PiHi k c t u) :
    t = 1 := by sorry

end QualityEncroach.FixedCost
