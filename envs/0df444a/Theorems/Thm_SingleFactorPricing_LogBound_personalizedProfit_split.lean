-- Prove2me | Theorems.Thm_SingleFactorPricing_LogBound_personalizedProfit_split
-- name    : SingleFactorPricing.LogBound.personalizedProfit_split
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:47.03363+00:00
-- url     : https://prove2.me/theorems/56c3e554-f16c-4caf-a356-fc32c89de899
-- title:
--   §2, p.4 — $\bar{\mathcal R}=q_{\min}G(q_{\min})+\int_{q_{\min}}^{q_{\max}}G(q)\,dq$
-- statement:
--   Let $q_{\min}>0$ and $q_{\max}$ be the infimum and supremum of the ratios $\bar p_{t,i}/f_i$. Then:
--
--   1. $\delta_{t,i}(q)=1$ for all $q\in[0,q_{\min}]$;
--   2. $\delta_{t,i}(q)=0$ for all $q>q_{\max}$;
--   3. the personalized profit splits as
--
--   $$
--   \bar{\mathcal R}=q_{\min}G(q_{\min})+\int_{q_{\min}}^{q_{\max}}G(q)\,dq .
--   $$
--
--   The first term collects the range of $q$ on which no pair has been filtered out, and the second is the range that produces the logarithm in Theorem 1.
--
--   Differences from the source:
--   - generalization: finitely many types $M$ with weights $\theta_j>0$ → any probability space $(T,\mu)$ of types; reason: the remark on p.5 extends the result to continuous types; $T=$ `Fin m` with `KallMayerSLP.ICC.discreteLaw θ id` is the printed case
--   - generalization: $\bar p^j$ optimal → positive prices, no optimality, A1 or non-negativity of demand; reason: none is used; the printed case has them
--   - generalization: $q_{\min}$, $q_{\max}$ a min and a max → `IsGLB` and `IsLUB` of the ratios, with $0<q_{\min}$; reason: they equal the min and max for finite $T$; for general $T$ this is the condition of p.5
--   - encoding: finite sums, no regularity stated → measurability of $\bar p$ and integrability of the optimal demands; reason: automatic for finitely many types; they rule out junk Bochner integrals only
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.4

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_personalizedProfit
import Definitions.Def_SingleFactorPricing_LogBound_filteredDemand
import Definitions.Def_SingleFactorPricing_LogBound_filterIndicator
import Definitions.Def_SingleFactorPricing_LogBound_priceRatios

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **M3: the split at `q_min`.** Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.4: "Notice that
`δ_ij(q) = 1` for all `q ∈ [0, q_min]` and `δ_ij(q) = 0` for all `q > q_max`, where
`q_min := min_{i∈N,j∈M} p̄_ij/f_i` and `q_max := max_{i∈N,j∈M} p̄_ij/f_i`. This implies that
`R̄ = q_min G(q_min) + ∫_{q_min}^{q_max} G(q)dq`."

**Formalization Note.** `q_min` and `q_max` are the `IsGLB` and `IsLUB` of the ratios, and
`0 < qmin` is the p.5 condition for a general type space. The non-strict inequality in `δ` is what
gives `δ = 1` at `q = q_min`. -/
theorem personalizedProfit_split {N T : Type*} [Fintype N] [Nonempty N] [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ)
    (pbar : T → N → ℝ) (qmin qmax : ℝ) (hf : ∀ i, 0 < f i) (hp : ∀ t i, 0 < pbar t i)
    (hmeas : ∀ i, Measurable fun t => pbar t i)
    (hint : ∀ i, Integrable (fun t => d t (pbar t) i) μ)
    (hqmin : 0 < qmin) (hglb : IsGLB (priceRatios f pbar) qmin)
    (hlub : IsLUB (priceRatios f pbar) qmax) :
    (∀ t i q, q ∈ Set.Icc 0 qmin → filterIndicator f pbar t i q = 1) ∧
      (∀ t i q, qmax < q → filterIndicator f pbar t i q = 0) ∧
      personalizedProfit μ d pbar =
        qmin * filteredDemand μ d f pbar qmin + ∫ q in qmin..qmax, filteredDemand μ d f pbar q := by sorry

end SingleFactorPricing.LogBound
