-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_3_3
-- name    : StratifyMarkets.DoubleAuction.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:53:42.340267+00:00
-- url     : https://prove2.me/theorems/76bfaef0-a846-4bdb-b40b-427668170cca
-- title:
--   Lemma 3.3 — monotonicity of optimal seller prices: F̄(c) > 0 and c < c′ imply s_c ≤ s_{c′}
-- statement:
--   Let $(F,G)$ be a bilateral trade instance and $\bar F(s)=\Pr[v\ge s]$. Let $0\le c<c'\le1$, and let $s_c\in\arg\max_{s\in[0,1]}(s-c)\bar F(s)$ and $s_{c'}\in\arg\max_{s\in[0,1]}(s-c')\bar F(s)$ be any profit-maximizing prices. If $\bar F(c)>0$, then
--   $$s_c\le s_{c'}.$$
--   It makes the seller intervals of Lemma 3.5's construction consecutive.
--
--   Differences from the source:
--   - encoding: F and G are continuous distributions supported on [0, 1], v and c independent → a `BTInstance`: probability measures μB, μS with no atoms (`NullSingletonClass`) and mass 1 on [0, 1]; expectations over the product `μS.prod μB`; reason: a CDF is continuous exactly when its law has no atoms; same instances
--   - encoding: s_c ∈ argmax_{s∈[0,1]} (s − c)·F̄(s) → sc ∈ [0, 1] with `IsMaxOn (fun s => (s − c) * Fbar s) (Icc 0 1) sc`; reason: the same set of maximizers
--   - encoding: F̄(c), 'the probability that the buyer's value is above c' → Fbar c = Pr[v ≥ c]; reason: Pr[v = c] = 0 by continuity, so ≥ and > give the same number
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 18, Lemma 3.3

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Bilateral

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 3.3 (p. 18): for `0 ≤ c < c' ≤ 1` and any maximizers `s_c`, `s_{c'}` over `[0, 1]` of
`s ↦ (s − c) F̄(s)` and `s ↦ (s − c') F̄(s)`, if `F̄(c) > 0` then `s_c ≤ s_{c'}`. -/
theorem lemma_3_3 (I : BTInstance) (c c' : ℝ) (hc : 0 ≤ c) (hcc' : c < c') (hc' : c' ≤ 1)
    (sc sc' : ℝ) (hsc : sc ∈ Set.Icc (0 : ℝ) 1)
    (hsc_max : IsMaxOn (fun s => (s - c) * I.Fbar s) (Set.Icc 0 1) sc)
    (hsc' : sc' ∈ Set.Icc (0 : ℝ) 1)
    (hsc'_max : IsMaxOn (fun s => (s - c') * I.Fbar s) (Set.Icc 0 1) sc')
    (hF : 0 < I.Fbar c) : sc ≤ sc' := by sorry

end StratifyMarkets.DoubleAuction
