-- Prove2me | Theorems.Thm_TsallisINF_Half_lemma_11_part_1
-- name    : TsallisINF.Half.lemma_11_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:57.347913+00:00
-- url     : https://prove2.me/theorems/db69930c-576e-45f8-8511-93cd1d2466c6
-- title:
--   Lemma 11, part 1: IW instantaneous stability
-- statement:
--   Consider half-Tsallis-INF with symmetric regularization, a positive learning-rate sequence, and importance-weighted loss estimates. At every round $t\ge1$, its expected instantaneous stability $S_t$ obeys
--
--   $$
--   S_t\le\min\left\{\sum_{i=1}^K\frac{\eta_t}{2}\sqrt{\mathbb E[w_{t,i}]},\;1\right\}.
--   $$
--
--   Here $S_t=\mathbb E[\ell_{t,I_t}+\Phi_t(-\widehat L_t)-\Phi_t(-\widehat L_{t-1})]$. This controls the early rounds in Theorem 1, when its RV estimator has zero baseline and equals the IW estimator.
--
--   **Formalization Note** This is the $\alpha=1/2$, $\xi_i=1$ instance of the paper's general first part. The expectation includes a randomized adaptive adversary and the learner's action draws.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 20, Lemma 11, part 1

import Mathlib
import Definitions.Def_TsallisINF_Half_Setting

open MeasureTheory

namespace TsallisINF.Half

/-- Lemma 11, part 1, specialized to alpha one half and symmetric regularization. -/
theorem lemma_11_part_1 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (hadv : ∀ t, 1 ≤ t → ∀ h i, Measurable (fun ω => (adv ω).val t h i))
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (η : ℕ → ℝ) (hη : ∀ s, 1 ≤ s → 0 < η s)
    (hW : IsTsallisINF η (estIW adv W) W)
    (t : ℕ) (ht : 1 ≤ t) :
    stability μ adv W (⟨0, hK⟩ : Fin K) η (estIW adv W) t ≤
      min (∑ i : Fin K, η t / 2 * Real.sqrt
        (expect μ W (⟨0, hK⟩ : Fin K) t (fun ω h => W t ω h i))) 1 := by sorry

end TsallisINF.Half
