-- Prove2me | Theorems.Thm_UnderstandingML_gd_lemma
-- name    : UnderstandingML.gd_lemma
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:23:48.357393+00:00
-- url     : https://prove2.me/theorems/8b9c0673-9f52-4627-9ae4-2a641a654a69
-- title:
--   Lemma 14.1: for w⁽¹⁾ = 0 and w⁽ᵗ⁺¹⁾ = w⁽ᵗ⁾ − ηvₜ, ∑ₜ⟨w⁽ᵗ⁾ − w⋆, vₜ⟩ ≤ ‖w⋆‖²/(2η) + (η/2)∑ₜ‖vₜ‖²; with ‖vₜ‖ ≤ ρ, ‖w⋆‖ ≤ B and η = B/(ρ√T) the average is ≤ Bρ/√T
-- statement:
--   **Lemma 14.1.** Let $v_1, \dots, v_T$ be an arbitrary sequence of vectors. Any algorithm with an initialization $w^{(1)} = 0$ and an update rule of the form $w^{(t+1)} = w^{(t)} - \eta v_t$ (14.4) satisfies
--   $$\sum_{t=1}^T \langle w^{(t)} - w^\star, v_t\rangle \le \frac{\|w^\star\|^2}{2\eta} + \frac\eta2\sum_{t=1}^T \|v_t\|^2. \tag{14.5}$$
--   In particular, for every $B, \rho > 0$, if for all $t$ we have $\|v_t\| \le \rho$ and if we set $\eta = \sqrt{B^2/(\rho^2 T)}$, then for every $w^\star$ with $\|w^\star\| \le B$ we have $\frac1T\sum_{t=1}^T \langle w^{(t)} - w^\star, v_t\rangle \le \frac{B\rho}{\sqrt T}$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §14.1.1 p. 187, Lemma 14.1 with its proof

import Definitions.Def_UnderstandingML_SGD

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 14.1** (p. 187). Let `v₁, …, v_T` be an arbitrary sequence of vectors. Any algorithm
with an initialization `w⁽¹⁾ = 0` and an update rule `w⁽ᵗ⁺¹⁾ = w⁽ᵗ⁾ − η vₜ` (14.4) satisfies
`∑ₜ ⟨w⁽ᵗ⁾ − w⋆, vₜ⟩ ≤ ‖w⋆‖²/(2η) + (η/2) ∑ₜ ‖vₜ‖²` (14.5). In particular, for every `B, ρ > 0`,
if `‖vₜ‖ ≤ ρ` for all `t` and `η = √(B²/(ρ²T))`, then for every `w⋆` with `‖w⋆‖ ≤ B`,
`(1/T) ∑ₜ ⟨w⁽ᵗ⁾ − w⋆, vₜ⟩ ≤ Bρ/√T`. Iterates indexed from `0`. -/
theorem gd_lemma {d : ℕ} (v : ℕ → Vec d) (T : ℕ) (wstar : Vec d) :
    (∀ η : ℝ, 0 < η →
      ∑ t ∈ Finset.range T, ⟪gdIterates η v t - wstar, v t⟫_ℝ ≤
        ‖wstar‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖v t‖ ^ 2) ∧
    ∀ B ρ : ℝ, 0 < B → 0 < ρ → (∀ t < T, ‖v t‖ ≤ ρ) → ‖wstar‖ ≤ B → 0 < T →
      (∑ t ∈ Finset.range T, ⟪gdIterates (B / (ρ * Real.sqrt T)) v t - wstar, v t⟫_ℝ) / T ≤
        B * ρ / Real.sqrt T := by sorry

end UnderstandingML
