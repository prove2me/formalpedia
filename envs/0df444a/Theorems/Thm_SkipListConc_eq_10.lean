-- Prove2me | Theorems.Thm_SkipListConc_eq_10
-- name    : SkipListConc.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:55:26.228933+00:00
-- url     : https://prove2.me/theorems/b86819ab-808e-4671-88e8-c338d4ad0b8c
-- title:
--   Eq. (10) — on $E_1=\{H^{\mathrm{seq}}_{\max}\le L\}$, $\sum_t\mathrm{cost}_t(x_t)\le W_{\mathrm{lev}}+C_{\mathrm{hor}}$
-- statement:
--   Fix $0<p<1$, an operation sequence $\sigma$ of length $F$ and a cutoff $L\ge1$. Heights never decrease, so the maximum height over the whole sequence is $H^{\mathrm{seq}}_{\max}=\max_xH_x(f_x)$. On the event $E_1=\{H^{\mathrm{seq}}_{\max}\le L\}$,
--   $$
--   \sum_{t=1}^{F}\mathrm{cost}_t(x_t)\ \le\ W_{\mathrm{lev}}+C_{\mathrm{hor}} .
--   $$
--
--   Differences from the source:
--   - generalization: heights following Definition 1.1 → every realization ξ of the randomness (no law assumed); reason: the inequality is pointwise; the source's case is an instance
--   - encoding: on E_1 → for every outcome with H_x(f_x) ≤ L for every item x of σ; reason: the definition of E_1
--   - encoding: cost_t(x_t), the levels a search visits plus its steps along levels → searchCost in closed form ∑_{ℓ=s_t}^{H_max(t)} (1 + steps on ℓ) over the items present (inserted at or before t), the target at its served height; reason: the source's definition (pp.4–5); checked on Figure 1
--   - encoding: A_{ℓ,t}, the left steps on level ℓ ≥ s_t of the backward walk of charge t → gapA, the levelSteps count of the time-t configuration at level ℓ (nodes y ≤ x_t of time-t height ≥ ℓ with no node of height ≥ ℓ+1 between y and x_t), charges t : Fin σ.length (0-based); reason: the same number as the walk on every level ℓ ≥ s_t, the forced first step on level s_t included and 0 above the maximum height (pp.26–27)
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Eq. (10), §4.5.4, p.29

import Mathlib
import Definitions.Def_SkipListConc_height
import Definitions.Def_SkipListConc_totalCost
import Definitions.Def_SkipListConc_Wlev
import Definitions.Def_SkipListConc_Chor

namespace SkipListConc

/-- Equation (10) (cost on the cutoff event `E₁`) (Kapoor–Tanveer, *Counter-Free Self-Adjusting
Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
§4.5.4, p.29). Fix a cutoff `L` and let `E₁ = {H^seq_max ≤ L}`, `H^seq_max = max_x H_x(f_x)`. On
`E₁`, `∑_{t=1}^{F} cost_t(x_t) ≤ W_lev + C_hor`.

**Formalization Note** Pointwise, for every cutoff `L ≥ 1` and every noise realization `ξ`: on
every outcome where every item's final height is at most `L`. -/
theorem eq_10 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (L : ℕ) (hL : 1 ≤ L) :
    ∀ ω : Ω, (∀ x ∈ σ.toFinset, height p ξ x (σ.count x) ω ≤ L) →
      totalCost p ξ σ ω ≤ Wlev p ξ σ L ω + Chor p ξ σ L ω := by sorry

end SkipListConc
