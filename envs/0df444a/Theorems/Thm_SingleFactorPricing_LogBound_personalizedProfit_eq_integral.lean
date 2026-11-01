-- Prove2me | Theorems.Thm_SingleFactorPricing_LogBound_personalizedProfit_eq_integral
-- name    : SingleFactorPricing.LogBound.personalizedProfit_eq_integral
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:05.601316+00:00
-- url     : https://prove2.me/theorems/97c7defc-4431-4292-8996-94ecc7f79afd
-- title:
--   §2, p.4 — $\bar{\mathcal R}=\int_0^\infty G(q)\,dq$
-- statement:
--   Let $\mu$ be a probability measure on the types, $f$ a positive vector, and $\bar p$ positive prices, measurable in the type, with integrable optimal demands and with the ratios $\bar p_{t,i}/f_i$ bounded above. Then $G$ is integrable on $(0,\infty)$ and
--
--   $$
--   \bar{\mathcal R}=\int_0^\infty G(q)\,dq .
--   $$
--
--   This expresses the personalized profit as an integral of the filtered demand, the form in which A1 can be applied.
--
--   Differences from the source:
--   - generalization: finitely many types $M$ with weights $\theta_j>0$ → any probability space $(T,\mu)$ of types; reason: the remark on p.5 extends the result to continuous types; $T=$ `Fin m` with `KallMayerSLP.ICC.discreteLaw θ id` is the printed case
--   - generalization: $\bar p^j$ optimal → positive prices, no optimality, A1 or non-negativity of demand; reason: none is used; the printed case has them
--   - generalization: $q_{\max}$ a finite maximum → the ratios are bounded above; reason: the same condition for finite $T$, and the p.5 condition for general $T$
--   - encoding: finite sums, no regularity stated → measurability of $\bar p$ and integrability of the optimal demands; reason: automatic for finitely many types; they rule out junk Bochner integrals only
--   - encoding: $\int_0^\infty$ → integral over `Set.Ioi 0`, with integrability of $G$ added to the conclusion; reason: the same integral; integrability makes the Bochner value meaningful
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.4

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_personalizedProfit
import Definitions.Def_SingleFactorPricing_LogBound_filteredDemand
import Definitions.Def_SingleFactorPricing_LogBound_priceRatios

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **M2: `R̄` as an integral.** Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.4: "Multiplying by
`θ_j` and adding over `j ∈ M` we conclude that `R̄ = ∫₀^∞ G(q)dq`."

**Formalization Note.** Over a general type space, this is an exchange of the integrals over the
types and over `q`. It uses measurability of the prices, integrability of the optimal demands and
a finite upper bound on the ratios `p̄_ij/f_i` (the `q_max` of p.4). Integrability of `G` on
`(0, ∞)` is part of the conclusion. -/
theorem personalizedProfit_eq_integral {N T : Type*} [Fintype N] [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ)
    (pbar : T → N → ℝ) (hf : ∀ i, 0 < f i) (hp : ∀ t i, 0 < pbar t i)
    (hmeas : ∀ i, Measurable fun t => pbar t i)
    (hint : ∀ i, Integrable (fun t => d t (pbar t) i) μ)
    (hbdd : BddAbove (priceRatios f pbar)) :
    IntegrableOn (filteredDemand μ d f pbar) (Set.Ioi 0) ∧
      personalizedProfit μ d pbar = ∫ q in Set.Ioi (0 : ℝ), filteredDemand μ d f pbar q := by sorry

end SingleFactorPricing.LogBound
