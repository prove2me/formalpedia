-- Prove2me | Theorems.Thm_TsallisINF_AdvAlpha_lemma_20
-- name    : TsallisINF.AdvAlpha.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:34:40.688383+00:00
-- url     : https://prove2.me/theorems/5ae895c4-9aeb-43f9-90f4-321147a55e7f
-- title:
--   Lemma 20, p. 41 — penalty of α-Tsallis-INF bounded by learning-rate increments of Ψ plus ⟨u − e_{i*_T}, L_T⟩
-- statement:
--   Let $\alpha\in(0,1)$, $\xi_1,\dots,\xi_K>0$, and let $\Psi(w)=-\sum_i (w_i^\alpha-\alpha w_i)/(\alpha(1-\alpha)\xi_i)$. Run α-Tsallis-INF with any conditionally unbiased loss estimators against a randomized adaptive adversary with losses in $[0,1]$, with learning rates $\eta_1,\dots,\eta_T>0$. Let $u,v\in\Delta^{K-1}$ be fixed and let $i^*_T$ be a best arm in expectation in hindsight. Then the **penalty** term satisfies
--   $$
--   \mathbb E\Big[\sum_{t=1}^T\big(\Phi_t(-\hat L_{t-1})-\Phi_t(-\hat L_t)-\ell_{t,i^*_T}\big)\Big]
--   \le\mathbb E\Big[\frac{\Psi(v)-\Psi(w_1)}{\eta_1}+\sum_{t=2}^T\big(\eta_t^{-1}-\eta_{t-1}^{-1}\big)\big(\Psi(v)-\Psi(w_t)\big)+\frac{\Psi(u)-\Psi(v)}{\eta_T}+\big\langle u-e_{i^*_T},L_T\big\rangle\Big],
--   $$
--   where $L_T=\sum_{t=1}^T\ell_t$ is the vector of cumulative losses and $e_{i^*_T}$ is the corresponding unit vector.
--
--   This is the standard reduction of the penalty term; Lemma 12 is derived from it by choosing $u$ and $v$.
--
--   **Formalization Note** The page writes $\langle u-e_{i^*_T},L_T\rangle$ outside the expectation; under an adaptive or randomized adversary $L_T$ is random, so it is placed inside the expectation (for a deterministic oblivious adversary the two readings coincide). The page states the lemma for $\alpha\in[0,1]$; it is stated here for $\alpha\in(0,1)$, where the displayed $\Psi$ is defined. The estimators are arbitrary, as on the page ("any unbiased loss estimators", Lemma 12): unbiasedness is conditional on the adversary seed and the action history before round $t$, the estimator of round $t$ depends on the actions through round $t$ only (as in Algorithm 1), and it is measurable with finite expected absolute value, so the expectations are genuine. Positivity of the learning rates is assumed on rounds $1,\dots,T$, the rounds that occur.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 41, Lemma 20

import Mathlib
import Definitions.Def_TsallisINF_AdvAlpha_Setting

namespace TsallisINF.AdvAlpha

theorem lemma_20 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (ξ : Fin K → ℝ) (hξ : ∀ i, 0 < ξ i)
    (η : ℕ → ℝ) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hest : TsallisINF.Half.IsUnbiased μ adv W ⟨0, hK⟩ est)
    (hest_causal : ∀ s, 1 ≤ s → ∀ ω h h',
      RegretBandits.Adversarial.AgreeBefore (s + 1) h h' → est s ω h = est s ω h')
    (hW : IsAlphaTsallisINF α ξ η est W)
    (T : ℕ) (hT : 1 ≤ T) (hη : ∀ t, 1 ≤ t → t ≤ T → 0 < η t)
    (u v : Fin K → ℝ) (hu : u ∈ stdSimplex ℝ (Fin K)) (hv : v ∈ stdSimplex ℝ (Fin K))
    (istarT : Fin K) (histar : TsallisINF.Half.IsBestInHindsight μ adv W ⟨0, hK⟩ T istarT) :
    TsallisINF.Half.expect μ W ⟨0, hK⟩ T (fun ω h => ∑ t ∈ Finset.Icc 1 T,
        (Phi α ξ (η t) (fun i => -TsallisINF.Half.Lhat est t ω h i) -
          Phi α ξ (η t) (fun i => -TsallisINF.Half.Lhat est (t + 1) ω h i) -
          (adv ω).val t h istarT)) ≤
      TsallisINF.Half.expect μ W ⟨0, hK⟩ T (fun ω h =>
        (tsallisPsi α ξ v - tsallisPsi α ξ (W 1 ω h)) / η 1 +
          ∑ t ∈ Finset.Icc 2 T,
            ((η t)⁻¹ - (η (t - 1))⁻¹) * (tsallisPsi α ξ v - tsallisPsi α ξ (W t ω h)) +
          (tsallisPsi α ξ u - tsallisPsi α ξ v) / η T +
          ((∑ i, u i * cumLoss adv T ω h i) - cumLoss adv T ω h istarT)) := by sorry

end TsallisINF.AdvAlpha
