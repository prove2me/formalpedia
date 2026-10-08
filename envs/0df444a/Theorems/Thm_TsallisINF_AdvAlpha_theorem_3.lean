-- Prove2me | Theorems.Thm_TsallisINF_AdvAlpha_theorem_3
-- name    : TsallisINF.AdvAlpha.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:34:48.547684+00:00
-- url     : https://prove2.me/theorems/50255f84-805e-4ed6-824f-39793b2b4ff0
-- title:
--   Theorem 3, pp. 11–12 — α-Tsallis-INF (symmetric, IW) has Reg_T ≤ 2√(min{1/(α−α²), log K/α, log T/(1−α)}·KT) + 1 for every T
-- statement:
--   Let $K\ge1$ and $\alpha\in(0,1)$. Run α-Tsallis-INF with the symmetric regularizer
--   $$
--   \Psi(w)=-\sum_{i=1}^K\frac{w_i^\alpha-\alpha w_i}{\alpha(1-\alpha)},\qquad \Psi_t=\Psi/\eta_t,
--   $$
--   importance-weighted loss estimators $\hat\ell_{t,i}=\mathbb 1(I_t=i)\ell_{t,i}/w_{t,i}$, and the learning rate
--   $$
--   \eta_t=\sqrt{\frac{K^{1-2\alpha}-K^{-\alpha}}{1-\alpha}\cdot\frac{1-t^{-\alpha}}{\alpha t}},
--   $$
--   against an arbitrary adversary that chooses losses $\ell_{t}\in[0,1]^K$ adaptively, possibly using the learner's past actions and its own internal randomization. Then at every time $T\ge1$ the pseudo-regret satisfies
--   $$
--   \overline{Reg}_T\le2\sqrt{\min\Big\{\frac{1}{\alpha-\alpha^2},\ \frac{\log K}{\alpha},\ \frac{\log T}{1-\alpha}\Big\}\,KT}+1 .
--   $$
--
--   The bound is anytime (the learning rate does not depend on $T$) and holds simultaneously for every $T$. For $\alpha=\tfrac12$ the minimum is at most $4$, so $\overline{Reg}_T\le 4\sqrt{KT}+1$; as $\alpha\to1$ it recovers the $\sqrt{KT\log K}$ rate of Exp3 and as $\alpha\to0$ the $\sqrt{KT\log T}$ rate of the log-barrier.
--
--   **Formalization Note** The page states Theorem 3 for $\alpha\in[0,1]$, with the boundary learning rates defined as limits; this statement covers $\alpha\in(0,1)$, where every formula is defined, and the boundary cases are the companion theorems `theorem_3_alpha_one` and `theorem_3_alpha_zero`. The learning rate vanishes at $t=1$; the algorithm's predicate then makes $w_1$ the minimizer of $\Psi$ over the simplex, i.e. the uniform distribution, the initialisation of online mirror descent (§3.1). Losses lie in $[0,1]$ (Section 2). The adversary's seed space carries a probability measure and losses are measurable in the seed.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, pp. 11–12, Theorem 3

import Mathlib
import Definitions.Def_TsallisINF_AdvAlpha_Setting

namespace TsallisINF.AdvAlpha

theorem theorem_3 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α (fun _ => 1) (etaThm3 α K) (TsallisINF.Half.estIW adv W) W)
    (T : ℕ) (hT : 1 ≤ T) :
    TsallisINF.Half.pseudoRegret μ adv W ⟨0, hK⟩ T ≤
      2 * Real.sqrt (min (min (1 / (α - α ^ 2)) (Real.log K / α)) (Real.log T / (1 - α)) *
        K * T) + 1 := by sorry

end TsallisINF.AdvAlpha
