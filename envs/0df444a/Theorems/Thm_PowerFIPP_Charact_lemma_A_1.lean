-- Prove2me | Theorems.Thm_PowerFIPP_Charact_lemma_A_1
-- name    : PowerFIPP.Charact.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:29.179578+00:00
-- url     : https://prove2.me/theorems/d5798c49-dd7c-47c7-8578-1b4b201db827
-- title:
--   Lemma A.1, p. 27 — class (DL) iff, for every T, an L¹ bound and a uniform ε–δ bound over stopping times τ ≤ T
-- statement:
--   Let $Q$ be a probability measure on a filtered space $(\Omega,\mathcal F,\mathbb F)$ and, for $T\in(0,\infty)$, let $\mathcal T_T$ be the set of $\mathbb F$-stopping times $\tau\le T$. A progressively measurable real process $\zeta=(\zeta_t)_{t\ge0}$ is of class (DL) under $Q$ (for every $T$, $\{\zeta_\tau:\tau\in\mathcal T_T\}$ is uniformly integrable) if and only if, for every $T\in(0,\infty)$,
--   1. $\displaystyle\sup_{\tau\in\mathcal T_T}E^Q\big[|\zeta_\tau|\big]<+\infty$;
--   2. for every $\varepsilon>0$ there is $\delta>0$ such that whenever $A\in\mathcal F_T$ and $Q(A)\le\delta$,
--   $$\sup_{\tau\in\mathcal T_T,\ A\in\mathcal F_\tau}E^Q\big[|\zeta_\tau|\mathbf 1_A\big]\le\varepsilon.$$
--
--   The lemma is the tool for transferring the class (DL) clause of Definition 2.1 between $P$ and the equivalent measure $Q^M$ in Lemma 3.2.
--
--   **Formalization Note** The page says "an adapted process"; progressive measurability is added because the proof uses that $\zeta_\tau$ is $\mathcal F_\tau$-measurable (it takes $A=\{|\zeta_{\hat\tau}|>\lambda\}\in\mathcal F_{\hat\tau}$). Every process to which the paper applies the lemma is càdlàg and adapted, hence progressive. Class (DL) is defined in the classical form $\lim_{K\to\infty}\sup_\tau E^Q[|\zeta_\tau|\mathbf 1_{\{|\zeta_\tau|>K\}}]=0$, so the lemma is not a restatement of the definition.
-- source:
--   Bo, Capponi & Zhou, Power forward performance in semimartingale markets with stochastic integrated factors, arXiv:1811.11899v4, p. 27, Lemma A.1

import Mathlib
import Definitions.Def_PowerFIPP_Charact_Model

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace PowerFIPP.Charact

/-- **Lemma A.1** (p. 27). A progressively measurable process `ζ` is of class (DL) under the
probability measure `Q` iff for every `T ∈ (0, ∞)`: (i) `sup_{τ ∈ 𝒯_T} E^Q|ζ_τ| < ∞`; (ii) for
every `ε > 0` there is `δ > 0` such that `Q(A) ≤ δ`, `A ∈ 𝓕_T` imply
`sup_{τ ∈ 𝒯_T, A ∈ 𝓕_τ} E^Q[|ζ_τ| 1_A] ≤ ε`. -/
theorem lemma_A_1 {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (ζ : ℝ≥0 → Ω → ℝ)
    (hζ : IsStronglyProgressive ℱ ζ) :
    ClassDL Q ℱ (fun t ω => ‖ζ t ω‖ₑ) ↔
      ∀ T : ℝ≥0, 0 < T →
        (⨆ (τ : Ω → WithTop ℝ≥0) (_ : IsBoundedStop ℱ T τ),
            ∫⁻ ω, ‖stoppedValue ζ τ ω‖ₑ ∂Q) < ∞ ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ A : Set Ω, MeasurableSet[ℱ T] A →
          Q A ≤ ENNReal.ofReal δ →
          (⨆ (τ : Ω → WithTop ℝ≥0) (hτ : IsBoundedStop ℱ T τ)
              (_ : MeasurableSet[hτ.1.measurableSpace] A),
              ∫⁻ ω in A, ‖stoppedValue ζ τ ω‖ₑ ∂Q) ≤ ENNReal.ofReal ε := by sorry

end PowerFIPP.Charact
