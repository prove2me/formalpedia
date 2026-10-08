-- Prove2me | Theorems.Thm_RegretBandits_Stochastic_pseudo_regret_decomposition
-- name    : RegretBandits.Stochastic.pseudo_regret_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:19:39.844534+00:00
-- url     : https://prove2.me/theorems/7d8a2139-8004-45eb-96b3-9bf74894162b
-- title:
--   Pseudo-regret decomposition $\overline R_n=\sum_i\Delta_i\,\mathbb E\,T_i(n)$
-- statement:
--   Consider a stochastic bandit with $K\ge2$ arms of means $\mu_1,\dots,\mu_K$, let $\mu^*=\max_i\mu_i$, $\Delta_i=\mu^*-\mu_i$ the suboptimality gap of arm $i$, and $T_i(n)=\sum_{t=1}^n\mathbb 1_{I_t=i}$ the number of times arm $i$ is selected in the first $n$ rounds by a forecaster whose choices $I_t$ are random variables. Then
--   $$\overline R_n=\Big(\sum_{i=1}^K\mathbb E\,T_i(n)\Big)\mu^*-\mathbb E\sum_{i=1}^K T_i(n)\mu_i=\sum_{i=1}^K\Delta_i\,\mathbb E\,T_i(n).$$
--
--   This identity reduces a pseudo-regret bound to a bound on the expected number of pulls of each suboptimal arm, which is how Theorem 2.1 is proved.
--
--   **Formalization Note.** The pseudo-regret is $n\mu^*-\mathbb E\sum_{t=1}^n\mu_{I_t}$ as in (2.1). The arms $I_t$ are assumed measurable, so that the expectations are genuine.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 9, Section 2 (unnumbered display)

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_RegretBandits_Stochastic_model

namespace RegretBandits.Stochastic

open MeasureTheory ImprovedLinBandits.UCBDelta

/-- Pseudo-regret decomposition (Bubeck and Cesa-Bianchi, arXiv:1204.5721v2, Section 2, p. 9):
for any forecaster whose arms `I_t` are random variables,
`R̄_n = (∑_i 𝔼 T_i(n)) μ* - 𝔼 ∑_i T_i(n) μ_i = ∑_i Δ_i 𝔼 T_i(n)`. -/
theorem pseudo_regret_decomposition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (hK : 2 ≤ K) (μ : Fin K → ℝ) (I : ℕ → Ω → Fin K)
    (hI : ∀ t, Measurable (I t)) (n : ℕ) :
    pseudoRegretBar P μ I n =
        (∑ i, ∫ ω, (pullCount I i n ω : ℝ) ∂P) * bestMean μ
          - ∫ ω, ∑ i, (pullCount I i n ω : ℝ) * μ i ∂P ∧
      pseudoRegretBar P μ I n = ∑ i, gap μ i * ∫ ω, (pullCount I i n ω : ℝ) ∂P := by sorry

end RegretBandits.Stochastic
