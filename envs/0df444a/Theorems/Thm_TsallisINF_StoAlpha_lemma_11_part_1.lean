-- Prove2me | Theorems.Thm_TsallisINF_StoAlpha_lemma_11_part_1
-- name    : TsallisINF.StoAlpha.lemma_11_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:39:56.53211+00:00
-- url     : https://prove2.me/theorems/4f25d4c7-10ac-4c3f-b2cb-7ead62b70863
-- title:
--   Lemma 11 (part 1), p. 20 — the instantaneous stability with IW estimators is at most $\min\{\sum_i \frac{\eta_t\xi_i}{2}\mathbb E[w_{t,i}]^{1-\alpha},1\}$
-- statement:
--   Run α-Tsallis-INF with $\alpha\in(0,1)$, regularization parameters $\xi_i>0$, positive learning rates $\eta_s$ and importance-weighted (IW) loss estimators against a randomized adaptive adversary with losses in $[0,1]$. Then at every round $t\ge1$ the instantaneous stability satisfies
--   $$\mathbb E\Big[\ell_{t,I_t}+\Phi_t(-\hat L_t)-\Phi_t(-\hat L_{t-1})\Big]\le\min\Big\{\sum_{i=1}^K\frac{\eta_t\xi_i}{2}\,\mathbb E[w_{t,i}]^{1-\alpha},\ 1\Big\}.$$
--
--   This is the first case of Lemma 11; the proof of Theorem 4 uses it in the rounds $t\le T_0$, before the learning rate is small enough for the fourth case.
--
--   **Formalization Note** The expectations are taken with the law of the first $t$ rounds. The page allows $\alpha\in[0,1]$; the Lean statement takes $\alpha\in(0,1)$. "Positive learning rate" is read as $\eta_s>0$ for all $s\ge1$, which makes the weights of all rounds well defined.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 20, Lemma 11 (case 1 of 4)

import Mathlib
import Definitions.Def_TsallisINF_StoAlpha_Setting

open MeasureTheory

namespace TsallisINF.StoAlpha
theorem lemma_11_part_1 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (adv : Ω → Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (ξ : Fin K → ℝ) (hξ : ∀ i, 0 < ξ i)
    (η : ℕ → ℝ) (hη : ∀ s, 1 ≤ s → 0 < η s)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α ξ η (estIW adv W) W) (t : ℕ) (ht : 1 ≤ t) :
    instStability μ adv W ⟨0, hK⟩ α ξ η t ≤
      min (∑ i, η t * ξ i / 2 * meanW μ W ⟨0, hK⟩ t t i ^ (1 - α)) 1 := by sorry
end TsallisINF.StoAlpha
