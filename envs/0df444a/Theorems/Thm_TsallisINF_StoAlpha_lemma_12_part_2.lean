-- Prove2me | Theorems.Thm_TsallisINF_StoAlpha_lemma_12_part_2
-- name    : TsallisINF.StoAlpha.lemma_12_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:39:23.112875+00:00
-- url     : https://prove2.me/theorems/aa83fba5-bd83-4a5b-916c-32b896d8eae5
-- title:
--   Lemma 12 (part 2), pp. 20–21 — the penalty with an arbitrary regularizer and non-increasing rates, for any $x\ge 1$
-- statement:
--   Run α-Tsallis-INF with $\alpha\in(0,1)$, arbitrary regularization parameters $\xi_i>0$, a non-increasing sequence of positive learning rates $\eta_1\ge\eta_2\ge\dots>0$ and any causal, measurable, integrable unbiased loss estimator against a randomized adaptive adversary with losses in $[0,1]$. Let $T\ge1$, let $i^*_T$ be a best arm in expectation in hindsight, and let $x\ge1$. Then
--   $$\mathbb E\Big[\sum_{t=1}^T\Phi_t(-\hat L_{t-1})-\Phi_t(-\hat L_t)-\ell_{t,i^*_T}\Big]\le\frac{1-T^{-\alpha x}}{\alpha}\sum_{i\ne i^*_T}\Big(\frac{\mathbb E[w_{1,i}]^\alpha-\alpha\,\mathbb E[w_{1,i}]}{\eta_1\xi_i(1-\alpha)}+\sum_{t=2}^T\Big(\frac1{\eta_t}-\frac1{\eta_{t-1}}\Big)\frac{\mathbb E[w_{t,i}]^\alpha-\alpha\,\mathbb E[w_{t,i}]}{\xi_i(1-\alpha)}\Big)+T^{1-x}.$$
--
--   Unlike the first part, the bound involves only the arms other than $i^*_T$, which is what the self-bounding analysis of Theorem 4 needs (it uses $x=1$).
--
--   **Formalization Note** The page allows $x\in[1,\infty]$; the value $x=\infty$ (a limit case) is not covered, and the case used in Theorem 4 is $x=1$. The page allows $\alpha\in[0,1]$; the Lean statement takes $\alpha\in(0,1)$. The estimator's causality, measurability, integrability and unbiasedness spell out the bandit protocol's standing assumptions. All expectations use the law of the first $T$ rounds.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, pp. 20–21, Lemma 12 (part 2)

import Mathlib
import Definitions.Def_TsallisINF_StoAlpha_Setting

open MeasureTheory

namespace TsallisINF.StoAlpha
theorem lemma_12_part_2 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (adv : Ω → Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (ξ : Fin K → ℝ) (hξ : ∀ i, 0 < ξ i)
    (η : ℕ → ℝ) (hη : ∀ s, 1 ≤ s → 0 < η s)
    (hηanti : ∀ s t, 1 ≤ s → s ≤ t → η t ≤ η s)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hest : TsallisINF.Half.IsUnbiased μ adv W ⟨0, hK⟩ est)
    (hcausal : IsCausalEstimator est)
    (hW : IsAlphaTsallisINF α ξ η est W) (T : ℕ) (hT : 1 ≤ T)
    (istarT : Fin K) (hbest : IsBestInHindsight μ adv W ⟨0, hK⟩ T istarT)
    (x : ℝ) (hx : 1 ≤ x) :
    penaltyWith μ adv W ⟨0, hK⟩ α ξ η est T istarT ≤
      (1 - (T : ℝ) ^ (-(α * x))) / α *
        ∑ i ∈ Finset.univ.erase istarT,
          ((meanW μ W ⟨0, hK⟩ T 1 i ^ α - α * meanW μ W ⟨0, hK⟩ T 1 i) /
              (η 1 * ξ i * (1 - α)) +
            ∑ t ∈ Finset.Icc 2 T,
              (1 / η t - 1 / η (t - 1)) *
                (meanW μ W ⟨0, hK⟩ T t i ^ α - α * meanW μ W ⟨0, hK⟩ T t i) /
                  (ξ i * (1 - α))) +
        (T : ℝ) ^ (1 - x) := by sorry
end TsallisINF.StoAlpha
