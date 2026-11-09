-- Prove2me | Theorems.Thm_SecondBestMatch_lemma_4_1
-- name    : SecondBestMatch.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:35.657759+00:00
-- url     : https://prove2.me/theorems/eb080ff0-f029-4956-bc4c-84cb7a751b9b
-- title:
--   Lemma 4.1 — the first-best match of an agent is monotone in her report
-- statement:
--   Fix all reports in $[0,1]$ except one agent's report, and let $M^*$ be the tie-broken first-best matching.
--
--   (a) If buyer $i$ is matched to seller $j$ by $M^*(v_i,\boldsymbol t_{-i})$, then she is matched to the same seller $j$ by $M^*(v_i',\boldsymbol t_{-i})$ for every $v_i'>v_i$.
--
--   (b) If seller $j$ is matched to buyer $i$ by $M^*(c_j,\boldsymbol t_{-j})$, then she is matched to the same buyer $i$ by $M^*(c_j',\boldsymbol t_{-j})$ for every $c_j'<c_j$.
--
--   Differences from the source:
--   - encoding: $M^*$: welfare maximizer of minimum cardinality, then a fixed total order on $\mathcal F$ → `firstBest m rank` with a rank satisfying `IsCardTieOrder`; reason: such ranks are exactly the total orders refined by cardinality
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Lemma 4.1, p.12

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_IsCardTieOrder
import Definitions.Def_SecondBestMatch_InUnitCube

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Lemma 4.1** (monotonicity; Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.1, p.12). Fix all reports except one agent's report.
(a) If buyer `i` is matched to seller `j` by `M*(vᵢ, t₋ᵢ)`, then she is matched to the same seller
`j` by `M*(v'ᵢ, t₋ᵢ)` for every `v'ᵢ > vᵢ`. (b) If seller `j` is matched to buyer `i` by
`M*(cⱼ, t₋ⱼ)`, then she is matched to the same buyer `i` by `M*(c'ⱼ, t₋ⱼ)` for every `c'ⱼ < cⱼ`.

**Formalization Note** `M*` is `firstBest m rank` with a cardinality-first rank; reports are in
`[0, 1]`. -/
theorem lemma_4_1 {B S : Type*} [DecidableEq B] [DecidableEq S] (m : Market B S)
    (hm : IsUnitMarket m) (rank : Finset (B × S) → ℕ) (hrank : IsCardTieOrder m rank)
    (t : Profile B S) (ht : InUnitCube t) (i : B) (j : S) :
    (∀ v v' : ℝ, v ∈ Icc (0 : ℝ) 1 → v' ∈ Icc (0 : ℝ) 1 → v < v' →
      (i, j) ∈ firstBest m rank (updateBuyer t i v) →
        (i, j) ∈ firstBest m rank (updateBuyer t i v')) ∧
    (∀ c c' : ℝ, c ∈ Icc (0 : ℝ) 1 → c' ∈ Icc (0 : ℝ) 1 → c' < c →
      (i, j) ∈ firstBest m rank (updateSeller t j c) →
        (i, j) ∈ firstBest m rank (updateSeller t j c')) := by sorry

end SecondBestMatch
