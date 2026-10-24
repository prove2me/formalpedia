-- Prove2me | Theorems.Thm_RetailerMarketplace_UnitFee_lemma_B_1
-- name    : RetailerMarketplace.UnitFee.lemma_B_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:49.288445+00:00
-- url     : https://prove2.me/theorems/defc3c39-aced-44a6-827b-0d896ab5d66f
-- title:
--   Lemma B.1, p. 18 — the monopolist will not charge a per-unit fee, t* = 0
-- statement:
--   Consider the retailer-led marketplace with a per-unit fee. Product valuations are distributed by a probability measure $\mu$ on $\mathbb R$ that is concentrated on $[c,\infty)$, has a density, has a finite mean, and charges every nonempty open interval of $[c,\infty)$; the marginal cost is $c>0$, the steering share is $\lambda\in[1/2,1]$ (Assumption 1), the capacity is $k\in[0,1]$, and $(k,\lambda)\ne(1,1)$. The monopolist chooses an ad valorem fee $f\in[0,1]$ and a per-unit fee $t\ge0$, and earns $\Pi_M(k,f,t)$, the supremum of his profit over all admissible allocations.
--
--   **Lemma B.1.** The monopolist will not charge a per-unit fee: if $(f^*,t^*)\in[0,1]\times[0,\infty)$ maximises $\Pi_M(k,\cdot,\cdot)$ over $[0,1]\times[0,\infty)$ and $f^*<1$, then
--   $$t^*=0.$$
--
--   The result says that, as long as subsidies are excluded, an ad valorem fee dominates a per-unit fee as a way for a retailer-led platform to extract revenue from third-party sellers.
--
--   **Formalization Note.** Two restrictions make explicit what the printed lemma tacitly assumes. (i) $f^*<1$: at $f=1$ no third-party seller enters for any $t\ge0$, so $t$ does not affect the monopolist's profit and $(1,t)$ with $t>0$ is optimal whenever $(1,0)$ is; the proof's alternative fee $f'$ is below $1$ exactly when $f^*<1$. (ii) $(k,\lambda)\ne(1,1)$: then $\pi_M^{SBMT}=v-c$, the monopolist covers every product, and every fee pair is optimal. Full support of $\mu$ on $[c,\infty)$ (the reading of $G^{-1}$ in the paper's display (3)), the density, the finite mean and $c>0$ are standing assumptions of the formalization, disclosed in the mission description. The statement is about every maximiser; it does not assert that a maximiser exists, as the paper does not. $\Pi_M$ is the genuine supremum over all measurable allocations, re-optimised at every fee pair.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 18 (PDF p. 20), Lemma B.1

import Mathlib
import Definitions.Def_RetailerMarketplace_UnitFee_Model
open MeasureTheory

namespace RetailerMarketplace.UnitFee

/-- Lemma B.1, p. 18: the monopolist will not charge a per-unit fee, `t* = 0`. Every fee pair
`(f*, t*) ∈ [0, 1] × [0, ∞)` maximising M's profit `Π_M` with an active marketplace (`f* < 1`)
has `t* = 0`. Products are distributed by a probability measure `μ` on `[c, ∞)` with a density,
full support on `[c, ∞)` and finite mean; `λ ≥ 1/2` (Assumption 1); the degenerate corner
`k = 1, λ = 1`, where every fee pair is optimal, is excluded. -/
theorem lemma_B_1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (c lam k : ℝ) (hc : 0 < c)
    (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) (hk : k ∈ Set.Icc (0 : ℝ) 1)
    (hsupp : μ (Set.Iio c) = 0) (hac : μ ≪ volume)
    (hint : Integrable (fun v : ℝ => v) μ)
    (hfull : ∀ a b : ℝ, c ≤ a → a < b → 0 < μ (Set.Ioo a b))
    (hnd : ¬ (k = 1 ∧ lam = 1)) :
    ∀ fs ts : ℝ, IsOptimalFee μ c lam k fs ts → fs < 1 → ts = 0 := by sorry

end RetailerMarketplace.UnitFee
