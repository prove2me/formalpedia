-- Prove2me | Theorems.Thm_TsallisINF_Half_lemma_12_part_2
-- name    : TsallisINF.Half.lemma_12_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:14.705803+00:00
-- url     : https://prove2.me/theorems/fb72245c-84ce-4884-b73b-60fc1059c4f4
-- title:
--   Lemma 12, part 2: refined penalty at x = infinity
-- statement:
--   Let half-Tsallis-INF use symmetric regularization, conditionally unbiased estimates and a positive, non-increasing learning-rate sequence. Let $i_T^*$ be a fixed arm with minimum expected cumulative loss. For $m_{t,i}=\mathbb E[w_{t,i}]$ and $T>1$, the $x=\infty$ instance of the refined penalty bound is
--
--   $$
--   P_T\le 2\sum_{i\ne i_T^*}\left[\frac{\sqrt{m_{1,i}}-m_{1,i}/2}{\eta_1/2}+\sum_{t=2}^T(\eta_t^{-1}-\eta_{t-1}^{-1})\frac{\sqrt{m_{t,i}}-m_{t,i}/2}{1/2}\right].
--   $$
--
--   At $T=1$ the limit of the paper’s right-hand side is $1$, which is included as a separate case. The bound exposes the weights of non-comparator arms and is used in the self-bounding analysis.
--
--   **Formalization Note** The estimator depends only on actions through its own round, is measurable, and has finite expected absolute size. The comparator remains the paper's best arm in expectation in hindsight, $i_T^*$; it is not silently replaced by the zero-gap arm in condition (4). The specialization fixes $\alpha=1/2$, $\xi_i=1$, and $x=\infty$.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, pp. 20–21, Lemma 12, part 2

import Mathlib
import Definitions.Def_TsallisINF_Half_Setting

open MeasureTheory

namespace TsallisINF.Half

/-- Lemma 12, part 2 at x infinity, alpha one half, and symmetric regularization. -/
theorem lemma_12_part_2 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
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
      if T = 1 then (1 : ℝ) else
      2 * ∑ i ∈ Finset.univ.erase istarT,
        ((Real.sqrt (expect μ W (⟨0, hK⟩ : Fin K) 1
            (fun ω h => W 1 ω h i)) -
            (1 / 2 : ℝ) * expect μ W (⟨0, hK⟩ : Fin K) 1
              (fun ω h => W 1 ω h i)) / (η 1 / 2) +
          ∑ t ∈ Finset.Icc 2 T,
            ((η t)⁻¹ - (η (t - 1))⁻¹) *
              ((Real.sqrt (expect μ W (⟨0, hK⟩ : Fin K) t
                  (fun ω h => W t ω h i)) -
                  (1 / 2 : ℝ) * expect μ W (⟨0, hK⟩ : Fin K) t
                    (fun ω h => W t ω h i)) / (1 / 2 : ℝ))) := by sorry

end TsallisINF.Half
