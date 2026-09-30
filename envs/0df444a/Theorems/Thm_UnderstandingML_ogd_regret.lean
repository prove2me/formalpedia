-- Prove2me | Theorems.Thm_UnderstandingML_ogd_regret
-- name    : UnderstandingML.ogd_regret
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:14:41.347076+00:00
-- url     : https://prove2.me/theorems/fd9e56f6-3f4a-4a7e-9876-51697a4d435c
-- title:
--   Theorem 21.15: Online Gradient Descent has regret ≤ ‖w⋆‖²/(2η) + (η/2)∑‖vₜ‖²; with ρ-Lipschitz fₜ and η = 1/√T, ≤ ½(‖w⋆‖² + ρ²)√T; with B-bounded H and η = B/(ρ√T), ≤ Bρ√T
-- statement:
--   **Theorem 21.15.** The Online Gradient Descent algorithm enjoys the following regret bound for every $w^\star \in H$,
--   $$\operatorname{Regret}_A(w^\star, T) \le \frac{\|w^\star\|^2}{2\eta} + \frac{\eta}{2}\sum_{t=1}^T\|v_t\|^2.$$
--   If we further assume that $f_t$ is $\rho$-Lipschitz for all $t$, then setting $\eta = 1/\sqrt{T}$ yields $\operatorname{Regret}_A(w^\star, T) \le \tfrac12(\|w^\star\|^2 + \rho^2)\sqrt{T}$. If we further assume that $H$ is $B$-bounded and we set $\eta = \frac{B}{\rho\sqrt T}$ then $\operatorname{Regret}_A(H, T) \le B\rho\sqrt T$.
--
--   Formally: $H$ closed and convex, $v_t = g_t(w^{(t)})$ with $g_t(w)$ a subgradient of $f_t$ at $w$, iterates from $w^{(0)} = 0$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §21.3 p. 301, Theorem 21.15

import Definitions.Def_UnderstandingML_Online

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 21.15** (p. 301). The Online Gradient Descent algorithm enjoys the following
regret bound for every `w⋆ ∈ H`: `Regret_A(w⋆, T) ≤ ‖w⋆‖²/(2η) + (η/2) ∑ₜ ‖vₜ‖²`. If we further
assume that `fₜ` is `ρ`-Lipschitz for all `t`, then setting `η = 1/√T` yields
`Regret_A(w⋆, T) ≤ ½(‖w⋆‖² + ρ²)√T`. If we further assume that `H` is `B`-bounded and we set
`η = B/(ρ√T)` then `Regret_A(H, T) ≤ Bρ√T`.
`H` is closed, convex and contains `w⋆`; `vₜ = g t w⁽ᵗ⁾` with `g t w` a subgradient of `fₜ` at
`w`; iterates indexed from `0`. -/
theorem ogd_regret {d : ℕ} (H : Set (Vec d)) (hH : Convex ℝ H) (hHc : IsClosed H)
    (f : ℕ → Vec d → ℝ) (g : ℕ → Vec d → Vec d) (hg : ∀ t w, IsSubgradient (f t) w (g t w))
    (T : ℕ) (wstar : Vec d) (hw : wstar ∈ H) :
    (∀ η : ℝ, 0 < η →
      ∑ t ∈ Finset.range T, (f t (ogdIterates H η g t) - f t wstar) ≤
        ‖wstar‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖g t (ogdIterates H η g t)‖ ^ 2) ∧
    (∀ ρ : NNReal, 0 < T → (∀ t, LipschitzWith ρ (f t)) →
      ∑ t ∈ Finset.range T, (f t (ogdIterates H (1 / Real.sqrt T) g t) - f t wstar) ≤
        1 / 2 * (‖wstar‖ ^ 2 + (ρ : ℝ) ^ 2) * Real.sqrt T) ∧
    (∀ (ρ : NNReal) (B : ℝ), 0 < T → 0 < ρ → 0 < B → (∀ t, LipschitzWith ρ (f t)) →
      (∀ w ∈ H, ‖w‖ ≤ B) →
      ∑ t ∈ Finset.range T, (f t (ogdIterates H (B / (ρ * Real.sqrt T)) g t) - f t wstar) ≤
        B * ρ * Real.sqrt T) := by sorry

end UnderstandingML
