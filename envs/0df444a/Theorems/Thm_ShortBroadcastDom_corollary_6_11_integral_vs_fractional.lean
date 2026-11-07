-- Prove2me | Theorems.Thm_ShortBroadcastDom_corollary_6_11_integral_vs_fractional
-- name    : ShortBroadcastDom.corollary_6_11_integral_vs_fractional
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:05.811838+00:00
-- url     : https://prove2.me/theorems/67ab6a1b-e5f9-4d87-ba7d-6ae304faff84
-- title:
--   Corollary 6.11 — $\gamma_R(H)\le(2\lceil a\rceil+1)\tau_{R,c}(H)$, and a dominating set of the same cost bound
-- statement:
--   Under the hypotheses of Lemma 6.10 ($a\ge1$, every subgraph of $H$ of density at most $a$, demands $R$, positive costs $c$), let $\gamma_R(H)$ be the minimum size of a set dominating $R$.
--
--   1. If every cost is at least one, then $\gamma_R(H)\le(2\lceil a\rceil+1)\,\tau_{R,c}(H)$.
--   2. There is a set $D$ dominating $R$ with $\sum_{v\in D}c_v\le(2\lceil a\rceil+1)\,\tau_{R,c}(H)$.
--
--   This compares the integral benchmark of the initializer (Theorem 6.1) with the fractional optimum.
--
--   Differences from the source:
--   - encoding: γ_R(H) ≤ (2⌈a⌉+1)τ → there is a set D dominating R with |D| ≤ (2⌈a⌉+1)τ; reason: γ_R(H) is an attained minimum, so the two are equivalent
--   - reading: "There also exists a set dominating R whose cost is at most this same multiple" (after "If every cost is at least one") → stated for all positive costs; reason: the sentence is ambiguous about the cost ≥ 1 assumption; the stronger reading is taken, and the proof (Lemma 6.10 with q = 1) uses only positivity
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §6.4.1, p.35 (PDF p.38), Corollary 6.11

import Mathlib
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_tauOn

namespace ShortBroadcastDom

/-- **Corollary 6.11 (integral versus fractional covering).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §6.4.1, p.35 (PDF 38): "Under
the hypotheses of Lemma 6.10, let γR(H) be the minimum cardinality of a set dominating R. If every
cost is at least one, then γR(H) ≤ (2⌈a⌉ + 1)τR,c(H). There also exists a set dominating R whose
cost is at most this same multiple of τR,c(H)."

**Formalization Note** `γ_R(H) ≤ X` is stated as the existence of a set `D` dominating `R` with
`|D| ≤ X` (the minimum is attained). The second clause is stated under the hypotheses of Lemma 6.10
only (positive costs), the stronger of the two readings. -/
theorem corollary_6_11_integral_vs_fractional {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (a : ℝ) (ha : 1 ≤ a) (hH : SubgraphDensityLE a H) (R : Finset V) (c : V → ℝ)
    (hc : ∀ v, 0 < c v) :
    ((∀ v, 1 ≤ c v) → ∃ D : Finset V, DominatesSet H R D ∧
        (D.card : ℝ) ≤ (2 * (⌈a⌉₊ : ℝ) + 1) * tau H R c) ∧
      ∃ D : Finset V, DominatesSet H R D ∧ ∑ v ∈ D, c v ≤ (2 * (⌈a⌉₊ : ℝ) + 1) * tau H R c := by sorry

end ShortBroadcastDom
