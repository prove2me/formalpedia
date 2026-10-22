-- Prove2me | Theorems.Thm_RiskFunctionals_NestedAVaR_nested_avar_dual
-- name    : RiskFunctionals.NestedAVaR.nested_avar_dual
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:09.394996+00:00
-- url     : https://prove2.me/theorems/53934090-8630-4cb3-bf29-d396d368f7c2
-- title:
--   Proposition 3.35 — dual representation (3.49) of the nested average value-at-risk
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $\mathcal F_0=\{\emptyset,\Omega\}\subseteq\mathcal F_1\subseteq\dots\subseteq\mathcal F_T=\mathcal F$, let $\alpha\in(0,1]$ and let $Y=(Y_1,\dots,Y_T)$ with $Y_t\in L_1(\mathcal F_t)$. The nested average value-at-risk
--   $$\mathrm{n}\mathbb{AV@R}_\alpha(Y;\boldsymbol{\mathcal F})=\mathbb{AV@R}_\alpha(\cdot\mid\mathcal F_0)\circ\dots\circ\mathbb{AV@R}_\alpha(\cdot\mid\mathcal F_{T-1})\Big(\sum_{t=1}^TY_t\Big)$$
--   is well defined, and it has the dual representation
--   $$\mathrm{n}\mathbb{AV@R}_\alpha(Y;\boldsymbol{\mathcal F})=\inf\Big\{\mathbb E\big[(Y_1+\dots+Y_T)Z_T\big]:0\le Z_t\le\tfrac1\alpha Z_{t-1},\ \mathbb E(Z_t\mid\mathcal F_{t-1})=Z_{t-1},\ Z_0=1,\ t=1,\dots,T\Big\}.\tag{3.49}$$
--   The feasible processes $(Z_t)$ are nonnegative martingales with $Z_t\le\alpha^{-t}$.
--
--   The representation identifies the nested average value-at-risk as a coherent acceptability functional whose dual set is the set of martingale densities whose one-step growth is bounded by $1/\alpha$; it is the basis of the comparison with the multi-period average value-at-risk in Proposition 3.36.
--
--   **Formalization Note** "Well defined" is the first conjunct: some versions of the conditional average values-at-risk (defined implicitly by (2.54)) yield a value. The second conjunct says every value obtained from any versions equals the infimum; the infimum is over processes with $Z_t$ $\mathcal F_t$-measurable (implicit on the page) and is taken in `EReal`. The process is `Y : ℕ → Ω → ℝ`, of which `Y 1, …, Y T` are used. The proposition's last sentence (version-independence and information monotonicity (MA0)) is not part of this item: information monotonicity is the separate item `nested_avar_info_monotone`, and version-independence in the sense of Definition 3.25 rests on nested distributions, which are not formalized.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 156, Proposition 3.35, Eq. (3.49) (nested AV@R: Example 3.34, Eq. (3.48); setting: p. 154, §3.3.4)

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_AverageValueAtRisk

namespace RiskFunctionals.NestedAVaR

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 156,
Proposition 3.35, representation (3.49): the nested average value-at-risk (3.48) has the dual
representation
`n𝔸𝕍@ℝ_α(Y; 𝓕) = inf {𝔼[(Y₁ + ⋯ + Y_T) Z_T] : 0 ≤ Z_t ≤ (1/α) Z_{t−1},
  𝔼(Z_t | ℱ_{t−1}) = Z_{t−1}, Z₀ = 1, t = 1, …, T}`.
Setting of §3.3.4: `ℱ₀ = {∅, Ω}`, `ℱ_T = ℱ`, `0 < α ≤ 1`, `Y_t ∈ L₁(ℱ_t)`. The nested `𝔸𝕍@ℝ`
exists (some versions of the conditional `𝔸𝕍@ℝ`'s give a value), and every value equals the
infimum, which runs over `ℱ_t`-adapted `Z` and is taken in `EReal`. -/
theorem nested_avar_dual {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) (Y : ℕ → Ω → ℝ)
    (hY : ∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P 1 (Y t)) :
    (∃ v : ℝ, IsNestedAVaR ℱ P α T Y v) ∧
      ∀ v : ℝ, IsNestedAVaR ℱ P α T Y v →
        (v : EReal) = ⨅ Z ∈ NestedDualSet ℱ P α T,
          ((∫ ω, (∑ t ∈ Finset.Icc 1 T, Y t ω) * Z T ω ∂P : ℝ) : EReal) := by sorry

end RiskFunctionals.NestedAVaR
