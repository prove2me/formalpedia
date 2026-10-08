-- Prove2me | Theorems.Thm_TsallisINF_Half_lemma_19
-- name    : TsallisINF.Half.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:50.657828+00:00
-- url     : https://prove2.me/theorems/7de8c4f4-40bd-4426-871e-876b1742dc9b
-- title:
--   Lemma 19: pathwise stability of half-Tsallis-INF
-- statement:
--   Fix a round $t\ge1$ of symmetric half-Tsallis-INF, a realized seed and action history, and any real shift $x$. If $\eta_t>0$ and $\eta_t(\widehat\ell_{t,i}-x)\sqrt{w_{t,i}}\ge-1$ for every arm $i$, then
--
--   $$
--   \langle w_t,\widehat\ell_t\rangle+\Phi_t(-\widehat L_t)-\Phi_t(-\widehat L_{t-1})
--   \le\sum_i\left[\frac{\eta_t}{2}w_{t,i}^{3/2}(\widehat\ell_{t,i}-x)^2+
--   \frac{\eta_t^2}{2}w_{t,i}^2\max\{x-\widehat\ell_{t,i},0\}^3\right].
--   $$
--
--   This pathwise inequality is a source for the expected stability estimates of Lemma 11.
--
--   **Formalization Note** The statement fixes $\alpha=1/2$, $\xi_i=1$, and a positive learning rate. Every fractional power is applied to a simplex weight and thus has a nonnegative base.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 36, Lemma 19

import Mathlib
import Definitions.Def_TsallisINF_Half_Setting

namespace TsallisINF.Half

/-- Lemma 19: a pathwise stability bound for half-Tsallis regularization. -/
theorem lemma_19 {K : ℕ} (hK : 0 < K) {Ω : Type*}
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (η : ℕ → ℝ) (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsTsallisINF η est W)
    (t : ℕ) (ht : 1 ≤ t) (hη : 0 < η t)
    (ω : Ω) (h : ℕ → Fin K) (x : ℝ)
    (hx : ∀ i : Fin K,
      -1 ≤ η t * (est t ω h i - x) * Real.sqrt (W t ω h i)) :
    (∑ i : Fin K, W t ω h i * est t ω h i) +
        Phi η t (fun i => -Lhat est (t + 1) ω h i) -
        Phi η t (fun i => -Lhat est t ω h i) ≤
      ∑ i : Fin K,
        ((η t / 2) * (W t ω h i) ^ (3 / 2 : ℝ) *
          (est t ω h i - x) ^ 2 +
        ((η t) ^ 2 / 2) * (W t ω h i) ^ 2 *
          (max (x - est t ω h i) 0) ^ 3) := by sorry

end TsallisINF.Half
