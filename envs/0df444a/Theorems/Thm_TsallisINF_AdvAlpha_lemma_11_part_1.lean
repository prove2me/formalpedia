-- Prove2me | Theorems.Thm_TsallisINF_AdvAlpha_lemma_11_part_1
-- name    : TsallisINF.AdvAlpha.lemma_11_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:34:35.401385+00:00
-- url     : https://prove2.me/theorems/9641d9b7-f533-4327-a3e6-f510f89b5d42
-- title:
--   Lemma 11 part 1, p. 20 — stability of α-Tsallis-INF with IW estimators: E[ℓ_{t,I_t} + Φ_t(−L̂_t) − Φ_t(−L̂_{t−1})] ≤ min{Σ_i (η_tξ_i/2) E[w_{t,i}]^{1−α}, 1}
-- statement:
--   Let $\alpha\in(0,1)$ and let $\xi_1,\dots,\xi_K>0$. Run α-Tsallis-INF with regularizer $\Psi(w)=-\sum_i (w_i^\alpha-\alpha w_i)/(\alpha(1-\alpha)\xi_i)$, an arbitrary learning-rate sequence $(\eta_s)$, and importance-weighted loss estimators $\hat\ell_{s,i}=\mathbb 1(I_s=i)\ell_{s,i}/w_{s,i}$, against an arbitrary randomized adaptive adversary with losses in $[0,1]$. Let $t\ge1$ be a round with $\eta_t>0$ and let $\Phi_t(Y)=\max_{w\in\Delta^{K-1}}\langle w,Y\rangle-\Psi(w)/\eta_t$. Then the instantaneous **stability** term satisfies
--   $$
--   \mathbb E\Big[\ell_{t,I_t}+\Phi_t(-\hat L_t)-\Phi_t(-\hat L_{t-1})\Big]\le\min\Big\{\sum_{i=1}^K\frac{\eta_t\xi_i}{2}\,\mathbb E[w_{t,i}]^{1-\alpha},\;1\Big\},
--   $$
--   where the expectation is over the adversary's seed and the learner's first $t$ actions.
--
--   This is the stability bound used in the proof of Theorem 3; it is due to Abernethy et al. (2015).
--
--   **Formalization Note** The page states the inequality for $\alpha\in[0,1]$; it is stated here for $\alpha\in(0,1)$, where $\Psi$ is defined by the displayed formula (the boundary regularizers are limits). Only $\eta_t>0$ at the round in question is assumed, as on the page ("for any $\eta_t>0$"). The expectation uses horizon $t$.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 20, Lemma 11 (case 1 of 4)

import Mathlib
import Definitions.Def_TsallisINF_AdvAlpha_Setting

namespace TsallisINF.AdvAlpha

theorem lemma_11_part_1 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (ξ : Fin K → ℝ) (hξ : ∀ i, 0 < ξ i)
    (η : ℕ → ℝ) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α ξ η (TsallisINF.Half.estIW adv W) W)
    (t : ℕ) (ht : 1 ≤ t) (hηt : 0 < η t) :
    TsallisINF.Half.expect μ W ⟨0, hK⟩ t (fun ω h =>
        (adv ω).val t h (h t) +
          Phi α ξ (η t) (fun i => -TsallisINF.Half.Lhat (TsallisINF.Half.estIW adv W) (t + 1) ω h i) -
          Phi α ξ (η t) (fun i => -TsallisINF.Half.Lhat (TsallisINF.Half.estIW adv W) t ω h i)) ≤
      min (∑ i, η t * ξ i / 2 * (TsallisINF.Half.expect μ W ⟨0, hK⟩ t (fun ω h => W t ω h i)) ^ (1 - α))
        1 := by sorry

end TsallisINF.AdvAlpha
