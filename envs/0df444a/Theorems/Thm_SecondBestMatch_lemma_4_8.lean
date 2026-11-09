-- Prove2me | Theorems.Thm_SecondBestMatch_lemma_4_8
-- name    : SecondBestMatch.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:16.437614+00:00
-- url     : https://prove2.me/theorems/9206bc4a-0d8a-4ff4-812f-40b031bc8c81
-- title:
--   Lemma 4.8 (with Lemma 4.7) — $q^\alpha$ is feasible and monotone, so $q^\alpha\in\mathcal P$
-- statement:
--   Let the priors have finite support and $\alpha>0$. The allocation rule $q^\alpha$ of Eq. (3) selects, at every profile of the support product, a probability distribution over $\mathcal F$ (Lemma 4.7: every realization belongs to $\mathcal F$); for every buyer, the interim service induced by $q^\alpha$ is nondecreasing in her value, and for every seller it is nonincreasing in her cost. Hence
--   $$
--   q^\alpha\in\mathcal P .
--   $$
--
--   Differences from the source:
--   - encoding: $M^*$: welfare maximizer of minimum cardinality, then a fixed total order on $\mathcal F$ → `firstBest m rank` with a rank satisfying `IsCardTieOrder`; reason: such ranks are exactly the total orders refined by cardinality
--   - encoding: the finite type space → the support product (`InPolytope`); reason: the profiles of positive probability
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Lemma 4.8, p.16 (with Lemma 4.7, p.16)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_IsFiniteSupportMarket
import Definitions.Def_SecondBestMatch_IsCardTieOrder
import Definitions.Def_SecondBestMatch_InPolytope
import Definitions.Def_SecondBestMatch_qAlpha

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Lemma 4.8** (monotonicity), with **Lemma 4.7** (feasibility on the support product)
(Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.3, p.16). For every buyer, the interim service induced by `q^α` is nondecreasing in her
value. For every seller, it is nonincreasing in her cost. Hence `q^α ∈ 𝒫`.

**Formalization Note** `q^α ∈ 𝒫` includes Lemma 4.7: at every support profile `q^α` is a
probability distribution over `ℱ` (every realization belongs to `ℱ`). `M*` is `firstBest m rank`
with a cardinality-first rank. -/
theorem lemma_4_8 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S] (m : Market B S) (hm : IsUnitMarket m) (hfs : IsFiniteSupportMarket m)
    (rank : Finset (B × S) → ℕ) (hrank : IsCardTieOrder m rank) (α : ℝ) (hα : 0 < α) :
    InPolytope m (qAlpha m rank α) := by sorry

end SecondBestMatch
