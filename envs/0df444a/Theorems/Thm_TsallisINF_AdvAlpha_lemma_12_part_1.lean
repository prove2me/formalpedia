-- Prove2me | Theorems.Thm_TsallisINF_AdvAlpha_lemma_12_part_1
-- name    : TsallisINF.AdvAlpha.lemma_12_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:34:33.065354+00:00
-- url     : https://prove2.me/theorems/1354a93a-531e-476e-86e9-440bcbbf49d7
-- title:
--   Lemma 12 part 1, p. 20 — penalty of symmetric α-Tsallis-INF ≤ (K^{1−α} − 1)(1 − T^{−α})/((1 − α)αη_T) + 1
-- statement:
--   Let $\alpha\in(0,1)$ and consider α-Tsallis-INF with the symmetric regularizer $\Psi(w)=-\sum_i (w_i^\alpha-\alpha w_i)/(\alpha(1-\alpha))$, any conditionally unbiased loss estimators, and a non-increasing sequence of positive learning rates $\eta_1\ge\eta_2\ge\dots>0$, played against a randomized adaptive adversary with losses in $[0,1]$. For every horizon $T\ge1$ and every best arm in expectation in hindsight $i^*_T$,
--   $$
--   \mathbb E\Big[\sum_{t=1}^T\big(\Phi_t(-\hat L_{t-1})-\Phi_t(-\hat L_t)-\ell_{t,i^*_T}\big)\Big]\le\frac{(K^{1-\alpha}-1)(1-T^{-\alpha})}{(1-\alpha)\alpha\eta_T}+1 .
--   $$
--
--   Together with the stability bound, this is the second half of the proof of Theorem 3.
--
--   **Formalization Note** The page states the lemma for $\alpha\in[0,1]$; it is stated here for $\alpha\in(0,1)$, where the displayed $\Psi$ is defined. The estimators are arbitrary, as on the page: unbiasedness is conditional on the adversary seed and the action history before round $t$, the estimator of round $t$ depends on the actions through round $t$ only (as in Algorithm 1), and it is measurable with finite expected absolute value. The hypotheses on the learning rates are the page's: positive and non-increasing over the whole sequence $t\ge1$. Note that Theorem 3's learning rate does not satisfy them (it is $0$ at $t=1$ and, for small $\alpha$, increases between $t=2$ and $t=3$); this lemma is stated as printed.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 20, Lemma 12 part 1

import Mathlib
import Definitions.Def_TsallisINF_AdvAlpha_Setting

namespace TsallisINF.AdvAlpha

theorem lemma_12_part_1 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℕ → ℝ) (hη_pos : ∀ t, 1 ≤ t → 0 < η t) (hη_anti : ∀ t, 1 ≤ t → η (t + 1) ≤ η t)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hest : TsallisINF.Half.IsUnbiased μ adv W ⟨0, hK⟩ est)
    (hest_causal : ∀ s, 1 ≤ s → ∀ ω h h',
      RegretBandits.Adversarial.AgreeBefore (s + 1) h h' → est s ω h = est s ω h')
    (hW : IsAlphaTsallisINF α (fun _ => 1) η est W)
    (T : ℕ) (hT : 1 ≤ T)
    (istarT : Fin K) (histar : TsallisINF.Half.IsBestInHindsight μ adv W ⟨0, hK⟩ T istarT) :
    TsallisINF.Half.expect μ W ⟨0, hK⟩ T (fun ω h => ∑ t ∈ Finset.Icc 1 T,
        (Phi α (fun _ => 1) (η t) (fun i => -TsallisINF.Half.Lhat est t ω h i) -
          Phi α (fun _ => 1) (η t) (fun i => -TsallisINF.Half.Lhat est (t + 1) ω h i) -
          (adv ω).val t h istarT)) ≤
      ((K : ℝ) ^ (1 - α) - 1) * (1 - (T : ℝ) ^ (-α)) / ((1 - α) * α * η T) + 1 := by sorry

end TsallisINF.AdvAlpha
