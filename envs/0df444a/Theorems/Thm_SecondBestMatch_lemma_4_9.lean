-- Prove2me | Theorems.Thm_SecondBestMatch_lemma_4_9
-- name    : SecondBestMatch.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:20:27.429993+00:00
-- url     : https://prove2.me/theorems/0cd8f76c-1d67-4d3e-a6d9-a2b776523a24
-- title:
--   Lemma 4.9 — the Lagrangian value of $q^\alpha$ is at least $g_\alpha\,\mathrm{FB}$
-- statement:
--   Let the priors have finite support and $\alpha>0$. Then
--   $$
--   \mathcal G(q^\alpha)+\alpha\,\mathcal B(q^\alpha)\ \ge\ g_\alpha\,\mathrm{FB}\ \ge\ \tfrac12\,\mathrm{FB},\tag{4}
--   $$
--   where the second inequality is strict whenever $\mathrm{FB}>0$.
--
--   Differences from the source:
--   - encoding: $M^*$: welfare maximizer of minimum cardinality, then a fixed total order on $\mathcal F$ → `firstBest m rank` with a rank satisfying `IsCardTieOrder`; reason: such ranks are exactly the total orders refined by cardinality
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Lemma 4.9, p.17, Eq. (4)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_IsFiniteSupportMarket
import Definitions.Def_SecondBestMatch_IsCardTieOrder
import Definitions.Def_SecondBestMatch_qAlpha
import Definitions.Def_SecondBestMatch_ordGFT
import Definitions.Def_SecondBestMatch_virtGFT
import Definitions.Def_SecondBestMatch_gCoeff
import Definitions.Def_SecondBestMatch_firstBestGFT

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Lemma 4.9** (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.3, p.17, Eq. (4)). For every `α > 0`,
`𝒢(q^α) + α ℬ(q^α) ≥ g_α FB ≥ ½ FB`, where the second inequality is strict whenever `FB > 0`. -/
theorem lemma_4_9 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S] (m : Market B S) (hm : IsUnitMarket m) (hfs : IsFiniteSupportMarket m)
    (rank : Finset (B × S) → ℕ) (hrank : IsCardTieOrder m rank) (α : ℝ) (hα : 0 < α) :
    gCoeff α * firstBestGFT m ≤
        ordGFT m (qAlpha m rank α) + α * virtGFT m (qAlpha m rank α) ∧
      1 / 2 * firstBestGFT m ≤ gCoeff α * firstBestGFT m ∧
      (0 < firstBestGFT m → 1 / 2 * firstBestGFT m < gCoeff α * firstBestGFT m) := by sorry

end SecondBestMatch
