-- Prove2me | Theorems.Thm_TsallisINF_StoAlpha_lemma_11_part_4
-- name    : TsallisINF.StoAlpha.lemma_11_part_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:39:53.877892+00:00
-- url     : https://prove2.me/theorems/22acfb6f-4a34-4077-b2f3-d2949050e2fc
-- title:
--   Lemma 11 (part 4), p. 20 — if $\eta_t\xi_i\le 1/4$, the stability is at most $\sum_{i\ne j}(\frac{\eta_t\xi_i}{2}\mathbb E[w_{t,i}]^{1-\alpha}+\frac{\eta_t(\xi_j+2\xi_i)}{2}\mathbb E[w_{t,i}])$
-- statement:
--   Run α-Tsallis-INF with $\alpha\in(0,1)$, regularization parameters $\xi_i>0$, positive learning rates and importance-weighted (IW) loss estimators against a randomized adaptive adversary with losses in $[0,1]$. Let $t\ge1$ be a round with $\eta_t\xi_i\le\frac14$ for all $i$. Then for every arm $j$,
--   $$\mathbb E\Big[\ell_{t,I_t}+\Phi_t(-\hat L_t)-\Phi_t(-\hat L_{t-1})\Big]\le\sum_{i\ne j}\Big(\frac{\eta_t\xi_i}{2}\,\mathbb E[w_{t,i}]^{1-\alpha}+\frac{\eta_t(\xi_j+2\xi_i)}{2}\,\mathbb E[w_{t,i}]\Big).$$
--
--   The bound removes the arm $j$ from the concave part of the stability; applied with $j=i^*$ it is what allows the self-bounding argument of Theorem 4.
--
--   **Formalization Note** The page prints the coefficient $\eta_t(\xi_i+2\xi_j)/2$; the proof of Lemma 11 (p. 38) derives $\eta_t(\xi_j+2\xi_i)/2$, which is the form stated here. Appendix D uses the lemma with $j=i^*$ and reaches the same bound with either form. Expectations use the law of the first $t$ rounds; $\alpha\in(0,1)$ instead of the page's $[0,1]$.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 20, Lemma 11 (case 4 of 4); coefficient as derived in the proof, p. 38

import Mathlib
import Definitions.Def_TsallisINF_StoAlpha_Setting

open MeasureTheory

namespace TsallisINF.StoAlpha
theorem lemma_11_part_4 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (adv : Ω → Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (ξ : Fin K → ℝ) (hξ : ∀ i, 0 < ξ i)
    (η : ℕ → ℝ) (hη : ∀ s, 1 ≤ s → 0 < η s)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α ξ η (estIW adv W) W) (t : ℕ) (ht : 1 ≤ t)
    (hηξ : ∀ i, η t * ξ i ≤ 1 / 4) (j : Fin K) :
    instStability μ adv W ⟨0, hK⟩ α ξ η t ≤
      ∑ i ∈ Finset.univ.erase j,
        (η t * ξ i / 2 * meanW μ W ⟨0, hK⟩ t t i ^ (1 - α) +
          η t * (ξ j + 2 * ξ i) / 2 * meanW μ W ⟨0, hK⟩ t t i) := by sorry
end TsallisINF.StoAlpha
