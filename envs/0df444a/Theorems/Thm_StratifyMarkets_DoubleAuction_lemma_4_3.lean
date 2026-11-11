-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_3
-- name    : StratifyMarkets.DoubleAuction.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:53:55.222487+00:00
-- url     : https://prove2.me/theorems/7d1b8022-19a5-4c03-9d15-9ab3e4ff651e
-- title:
--   Lemma 4.3 — first-best decomposition for λ ≥ 4: FB ≤ Σ_i E[(v_i − p̄)_+] + Σ_j E[(p̲ − c_j)_+] + λ(p̄ − p̲)
-- statement:
--   Let a double auction instance have $\lambda\ge4$, where $\lambda=\mathbb E_{\mathbf v}[B_{\tilde p}]=\mathbb E_{\mathbf c}[S_{\tilde p}]$ at a balanced price $\tilde p$ (4.1), and let $\bar p$, $\underline p$ be excess-supply and excess-demand prices (4.2). Then
--   $$\mathrm{FB}\le\sum_{i=1}^n\mathbb E_{\mathbf v}\big[(v_i-\bar p)_+\big]+\sum_{j=1}^m\mathbb E_{\mathbf c}\big[(\underline p-c_j)_+\big]+\lambda\cdot(\bar p-\underline p).$$
--   It is the upper bound that Lemmas 4.4 and 4.5 approximate term by term.
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: λ defined in (4.1) from the balanced price p̃ → a balanced price `pt` (`IsBalancedPrice`: pt ∈ [0, 1], E_v[B_pt] = E_c[S_pt]) as a variable, with λ = `expB pt`; reason: p̃ need not be unique but λ is the same for every balanced price, and a balanced price exists by continuity; quantifying over every one is at least as strong as fixing one
--   - encoding: the excess-supply price p̄ and the excess-demand price p̲ of (4.2) → arbitrary `pbar`, `plow` ∈ [0, 1] satisfying (4.2) (`IsExcessSupplyPrice`, `IsExcessDemandPrice`); reason: (4.2) need not have a unique solution; every solution lies in [0, 1] when λ ≥ 4, and quantifying over all of them is at least as strong as fixing one
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 28, Lemma 4.3

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_Prices

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.3 (p. 28): if `λ ≥ 4` (`λ = E_𝐯[B_p̃]` at a balanced price `p̃`), then for every
excess-supply price `p̄` and excess-demand price `p̲`,
`FB ≤ Σ_i E_𝐯[(v_i − p̄)_+] + Σ_j E_𝐜[(p̲ − c_j)_+] + λ (p̄ − p̲)`. -/
theorem lemma_4_3 {n m : ℕ} (I : DAInstance n m) (pt pbar plow : ℝ)
    (hpt : I.IsBalancedPrice pt) (hlam : 4 ≤ I.expB pt)
    (hpbar : I.IsExcessSupplyPrice pbar) (hplow : I.IsExcessDemandPrice plow) :
    I.FB ≤ I.buyerSurplus pbar + I.sellerSurplus plow + I.expB pt * (pbar - plow) := by sorry

end StratifyMarkets.DoubleAuction
