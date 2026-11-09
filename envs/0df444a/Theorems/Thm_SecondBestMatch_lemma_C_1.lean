-- Prove2me | Theorems.Thm_SecondBestMatch_lemma_C_1
-- name    : SecondBestMatch.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:17.93529+00:00
-- url     : https://prove2.me/theorems/fb36367a-c422-43ff-85b9-ba884f0d641f
-- title:
--   Lemma C.1 — first-best loss under one-sided rounding
-- statement:
--   Let $\mathcal I$ be an instance with priors on $[0,1]$, $R_{\max} = \max_{M\in\mathcal F}|M|$, $\delta_n = 2^{-n}$, and let $\mathcal I_n$ be the one-sided rounded instance (buyer values rounded down to the grid $\delta_n\mathbb Z$, seller costs rounded up and capped at $1$). For every $n\ge1$,
--   $$
--   \mathrm{FB}(\mathcal I) - 2R_{\max}\delta_n\ \le\ \mathrm{FB}(\mathcal I_n)\ \le\ \mathrm{FB}(\mathcal I).
--   $$
--   In particular, $\mathrm{FB}(\mathcal I_n)\to\mathrm{FB}(\mathcal I)$ as $n\to\infty$.
--
--   Together with Lemma C.2 this reduces the half-efficiency bound to finite-support priors.
--
--   Differences from the source:
--   - encoding: the rounded instance with types $\underline v_{i,n}$, $\overline c_{j,n}$ → `roundedMarket m n`, whose priors are the pushforwards of the original priors under the rounding maps; reason: the law of the rounded type is the pushforward; same instance
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Lemma C.1, p.33, Eq. (21)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_firstBestGFT
import Definitions.Def_SecondBestMatch_maxTrades
import Definitions.Def_SecondBestMatch_roundedMarket

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Lemma C.1** (first-best loss under one-sided rounding; Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), App. C, p.33, Eq. (21)). For
every `n ≥ 1`, `FB(ℐ) − 2 R_max δ_n ≤ FB_n ≤ FB(ℐ)` with `δ_n = 2^{−n}` and `FB_n = FB(ℐ_n)`. In
particular, `FB_n → FB(ℐ)`. -/
theorem lemma_C_1 {B S : Type*} [Fintype B] [Fintype S] (m : Market B S) (hm : IsUnitMarket m) :
    (∀ n : ℕ, 1 ≤ n →
      firstBestGFT m - 2 * (maxTrades m : ℝ) * (2 : ℝ) ^ (-(n : ℤ)) ≤
          firstBestGFT (roundedMarket m n) ∧
        firstBestGFT (roundedMarket m n) ≤ firstBestGFT m) ∧
    Tendsto (fun n : ℕ => firstBestGFT (roundedMarket m n)) atTop (𝓝 (firstBestGFT m)) := by sorry

end SecondBestMatch
