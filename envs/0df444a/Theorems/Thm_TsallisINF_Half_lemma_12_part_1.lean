-- Prove2me | Theorems.Thm_TsallisINF_Half_lemma_12_part_1
-- name    : TsallisINF.Half.lemma_12_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:51.7925+00:00
-- url     : https://prove2.me/theorems/ea73c643-ff88-42fb-8e86-2d1abf974381
-- title:
--   Lemma 12, part 1: symmetric penalty bound
-- statement:
--   Let $K\ge1$, $T\ge1$, and let half-Tsallis-INF use any conditionally unbiased loss estimates and a positive, non-increasing learning-rate sequence. If $i_T^*$ minimizes expected cumulative loss among fixed arms, its penalty term $P_T$ satisfies
--
--   $$
--   P_T\le\frac{(\sqrt K-1)(1-T^{-1/2})}{(1/4)\eta_T}+1.
--   $$
--
--   The penalty is the expected sum of the potential differences $\Phi_t(-\widehat L_{t-1})-\Phi_t(-\widehat L_t)$ minus the loss of $i_T^*$. This bound supplies the adversarial part of Theorem 1.
--
--   **Formalization Note** This is the $\alpha=1/2$ instance of the symmetric regularizer formula. Conditional unbiasedness fixes the adversary seed and action history before averaging over the action at round $t$. The estimator depends only on actions through its own round, as Algorithm 1 requires. It is also measurable and has finite expected absolute size.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 20, Lemma 12, part 1

import Mathlib
import Definitions.Def_TsallisINF_Half_Setting

open MeasureTheory

namespace TsallisINF.Half

/-- Lemma 12, part 1, specialized to alpha one half and symmetric regularization. -/
theorem lemma_12_part_1 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (hadv : ∀ t, 1 ≤ t → ∀ h i, Measurable (fun ω => (adv ω).val t h i))
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (η : ℕ → ℝ) (hη : ∀ s, 1 ≤ s → 0 < η s)
    (hηmono : ∀ s, 1 ≤ s → η (s + 1) ≤ η s)
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hest : IsUnbiased μ adv W (⟨0, hK⟩ : Fin K) est)
    (hest_causal : ∀ s, 1 ≤ s → ∀ ω h h',
      RegretBandits.Adversarial.AgreeBefore (s + 1) h h' →
        est s ω h = est s ω h')
    (hW : IsTsallisINF η est W)
    (T : ℕ) (hT : 1 ≤ T) (istarT : Fin K)
    (hbest : IsBestInHindsight μ adv W (⟨0, hK⟩ : Fin K) T istarT) :
    penalty μ adv W (⟨0, hK⟩ : Fin K) η est T istarT ≤
      ((Real.sqrt (K : ℝ) - 1) * (1 - Real.sqrt (1 / (T : ℝ)))) /
        ((1 / 4 : ℝ) * η T) + 1 := by sorry

end TsallisINF.Half
