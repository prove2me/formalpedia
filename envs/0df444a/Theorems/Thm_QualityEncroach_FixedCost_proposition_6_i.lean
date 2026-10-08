-- Prove2me | Theorems.Thm_QualityEncroach_FixedCost_proposition_6_i
-- name    : QualityEncroach.FixedCost.proposition_6_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:54.890008+00:00
-- url     : https://prove2.me/theorems/426ad205-c461-45c5-be9e-be0e16ec4f3a
-- title:
--   Proposition 6(i), p. 20 — equal qualities under fixed-cost encroachment
-- statement:
--   Let $k>0$ be the quality-cost parameter and let $c>0$ be the manufacturer's cost per direct-channel unit. For any subgame-perfect strategy profile $\sigma$ of the three-stage fixed-quality-cost game, if the manufacturer makes a positive quantity of direct sales on the equilibrium path, then the ratio of retailer-channel to direct-channel quality is
--
--   $$t(\sigma)=1.$$
--
--   Thus active direct sales in equilibrium involve equal quality across the two channels, as asserted by Proposition 6(i).
--
--   **Formalization Note** The added $c>0$ excludes the manuscript's zero-cost degeneracy, at which its Claim 3 does not force $t=1$. Subgame perfection is required at every feasible history.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 20, Proposition 6(i); p. 37, proof

import Mathlib
import Definitions.Def_QualityEncroach_FixedCost_Game

namespace QualityEncroach.FixedCost

/-- Proposition 6(i), p. 20: in an encroaching subgame-perfect equilibrium
the two channels carry the same quality. The additional `0 < c` excludes the
zero-selling-cost counterexample to the printed statement. -/
theorem proposition_6_i (k c : ℝ) (hk : 0 < k) (hc : 0 < c)
    (σ : Profile) (hσ : IsSPE k c σ) (henc : 0 < σ.path.qM) :
    σ.t = 1 := by sorry

end QualityEncroach.FixedCost
