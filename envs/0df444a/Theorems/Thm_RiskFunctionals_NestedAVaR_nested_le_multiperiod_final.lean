-- Prove2me | Theorems.Thm_RiskFunctionals_NestedAVaR_nested_le_multiperiod_final
-- name    : RiskFunctionals.NestedAVaR.nested_le_multiperiod_final
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:09.847238+00:00
-- url     : https://prove2.me/theorems/76839d7e-43e4-47d9-a6cf-e730c6608756
-- title:
--   Proposition 3.36(ii) — for a final process, nested AV@R ≤ multi-period AV@R
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $\mathcal F_0=\{\emptyset,\Omega\}\subseteq\mathcal F_1\subseteq\dots\subseteq\mathcal F_T=\mathcal F$, let $\alpha\in(0,1]$ and $Y_t\in L_1(\mathcal F_t)$, $t=1,\dots,T$. If $Y$ is a **final process**, i.e. $Y_1=0,\dots,Y_{T-1}=0$, then
--   $$\mathrm{n}\mathbb{AV@R}_\alpha(Y;\boldsymbol{\mathcal F})\le\mathbb{AV@R}_\alpha(Y;\boldsymbol{\mathcal F}),$$
--   where the right side is the multi-period average value-at-risk $\sum_{t=1}^T\mathbb E[\mathbb{AV@R}_\alpha(Y_t\mid\mathcal F_{t-1})]$ of Definition 3.29 with all $\alpha_t=\alpha$, $c_t=1$.
--
--   For a single payment at the horizon, composing the conditional average values-at-risk is at least as pessimistic as averaging the last one.
--
--   **Formalization Note** $Y_t=0$ is almost sure equality. The inequality is claimed for every value of the two functionals (any versions of the conditional average values-at-risk).
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 157, Proposition 3.36(ii) (multi-period AV@R: p. 150, Definition 3.29)

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_AverageValueAtRisk

namespace RiskFunctionals.NestedAVaR

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 157,
Proposition 3.36(ii): if `Y` is a final process, i.e. `Y₁ = 0, …, Y_{T−1} = 0` (almost surely),
then `n𝔸𝕍@ℝ_α(Y; 𝓕) ≤ 𝔸𝕍@ℝ_α(Y; 𝓕)`, the right side being the multi-period `𝔸𝕍@ℝ` of
Definition 3.29 with all `α_t = α` and all `c_t = 1`. Setting of §3.3.4, `0 < α ≤ 1`,
`Y_t ∈ L₁(ℱ_t)`; claimed for every value of the two functionals. -/
theorem nested_le_multiperiod_final {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) (Y : ℕ → Ω → ℝ)
    (hY : ∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P 1 (Y t))
    (hfinal : ∀ t ∈ Finset.Icc 1 (T - 1), Y t =ᵐ[P] 0) (vn vm : ℝ)
    (hn : IsNestedAVaR ℱ P α T Y vn)
    (hm : IsMultiPeriodAVaR ℱ P (fun _ => α) (fun _ => 1) T Y vm) :
    vn ≤ vm := by sorry

end RiskFunctionals.NestedAVaR
