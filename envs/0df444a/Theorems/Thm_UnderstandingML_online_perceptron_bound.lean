-- Prove2me | Theorems.Thm_UnderstandingML_online_perceptron_bound
-- name    : UnderstandingML.online_perceptron_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:14:55.603693+00:00
-- url     : https://prove2.me/theorems/df68af50-1c35-4a36-b25b-50bbe409ee74
-- title:
--   Theorem 21.16: the online Perceptron's update rounds satisfy |M| ≤ ∑ₜ fₜ(w⋆) + R‖w⋆‖√(∑ₜ fₜ(w⋆)) + R²‖w⋆‖², and |M| ≤ R²‖w⋆‖² under margin 1
-- statement:
--   **Theorem 21.16.** Suppose that the Perceptron algorithm runs on a sequence $(x_1, y_1), \dots, (x_T, y_T)$ and let $R = \max_t\|x_t\|$. Let $M$ be the rounds on which the Perceptron errs and let $f_t(w) = \mathbb{1}[t \in M]\,[1 - y_t\langle w, x_t\rangle]_+$. Then, for every $w^\star$,
--   $$|M| \le \sum_t f_t(w^\star) + R\|w^\star\|\sqrt{\sum_t f_t(w^\star)} + R^2\|w^\star\|^2.$$
--   In particular, if there exists $w^\star$ such that $y_t\langle w^\star, x_t\rangle \ge 1$ for all $t$ then $|M| \le R^2\|w^\star\|^2$.
--
--   Formally: $y_t \in \{\pm1\}$, $M$ the set of update rounds $y_t\langle w^{(t)}, x_t\rangle \le 0$ (which contains every prediction mistake), and $R$ any bound on $\|x_t\|$, $t < T$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §21.4 pp. 303-304, Equation (21.6) and Theorem 21.16

import Definitions.Def_UnderstandingML_Online

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 21.16** (p. 304). Suppose that the Perceptron algorithm runs on a sequence
`(x₁, y₁), …, (x_T, y_T)` and let `R = maxₜ ‖xₜ‖`. Let `M` be the rounds on which the Perceptron
errs and let `fₜ(w) = 𝟙[t ∈ M] [1 − yₜ⟨w, xₜ⟩]₊`. Then, for every `w⋆`,
`|M| ≤ ∑ₜ fₜ(w⋆) + R‖w⋆‖ √(∑ₜ fₜ(w⋆)) + R²‖w⋆‖²`. In particular, if there exists `w⋆` such
that `yₜ⟨w⋆, xₜ⟩ ≥ 1` for all `t` then `|M| ≤ R²‖w⋆‖²`.
`M` is the set of update rounds `yₜ⟨w⁽ᵗ⁾, xₜ⟩ ≤ 0`; `R` is any bound on the norms. -/
theorem online_perceptron_bound {d : ℕ} (T : ℕ) (x : ℕ → Vec d) (y : ℕ → ℝ)
    (hy : ∀ t, y t = 1 ∨ y t = -1) (R : ℝ) (hR : ∀ t < T, ‖x t‖ ≤ R) (wstar : Vec d) :
    ((perceptronRounds x y T).card : ℝ) ≤
      (∑ t ∈ perceptronRounds x y T, max 0 (1 - y t * ⟪wstar, x t⟫_ℝ)) +
        R * ‖wstar‖ * Real.sqrt (∑ t ∈ perceptronRounds x y T, max 0 (1 - y t * ⟪wstar, x t⟫_ℝ)) +
        R ^ 2 * ‖wstar‖ ^ 2 ∧
    ((∀ t < T, 1 ≤ y t * ⟪wstar, x t⟫_ℝ) →
      ((perceptronRounds x y T).card : ℝ) ≤ R ^ 2 * ‖wstar‖ ^ 2) := by sorry

end UnderstandingML
