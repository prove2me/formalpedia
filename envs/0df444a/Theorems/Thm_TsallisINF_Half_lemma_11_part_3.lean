-- Prove2me | Theorems.Thm_TsallisINF_Half_lemma_11_part_3
-- name    : TsallisINF.Half.lemma_11_part_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:03.319838+00:00
-- url     : https://prove2.me/theorems/f96a563e-7eee-4a5f-9e20-9a91dc5a349c
-- title:
--   Lemma 11, part 3: RV instantaneous stability
-- statement:
--   Consider half-Tsallis-INF with symmetric regularization and reduced-variance loss estimates. At a round $t\ge1$ with $0<\eta_t\le1$, write $p_{t,i}=\mathbb E[w_{t,i}]$. Its instantaneous stability satisfies
--
--   $$
--   S_t\le\frac{7\eta_t^2}{8}K+\sum_{i=1}^K\frac{\eta_t}{8}\sqrt{p_{t,i}}(1-p_{t,i}).
--   $$
--
--   This is the per-round bound used for the RV part of Theorem 1. The expectation averages both the adversary's randomization and the learner's choices.
--
--   **Formalization Note** The regularizer has $\alpha=1/2$ and $\xi_i=1$; the RV baseline is selected precisely when $w_{t,i}\ge\eta_t^2$.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 20, Lemma 11, part 3

import Mathlib
import Definitions.Def_TsallisINF_Half_Setting

open MeasureTheory

namespace TsallisINF.Half

/-- Lemma 11, part 3, for reduced-variance estimators. -/
theorem lemma_11_part_3 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (hadv : ∀ t, 1 ≤ t → ∀ h i, Measurable (fun ω => (adv ω).val t h i))
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (η : ℕ → ℝ) (hη : ∀ s, 1 ≤ s → 0 < η s)
    (hW : IsTsallisINF η (estRV η adv W) W)
    (t : ℕ) (ht : 1 ≤ t) (hηt : η t ≤ 1) :
    stability μ adv W (⟨0, hK⟩ : Fin K) η (estRV η adv W) t ≤
      (7 * (η t) ^ 2 / 8) * (K : ℝ) +
        ∑ i : Fin K, (η t / 8) *
          Real.sqrt (expect μ W (⟨0, hK⟩ : Fin K) t
            (fun ω h => W t ω h i)) *
          (1 - expect μ W (⟨0, hK⟩ : Fin K) t
            (fun ω h => W t ω h i)) := by sorry

end TsallisINF.Half
