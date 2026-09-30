-- Prove2me | Theorems.Thm_UnderstandingML_fritz_john
-- name    : UnderstandingML.fritz_john
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:40:52.183893+00:00
-- url     : https://prove2.me/theorems/789b3fe9-090a-4ec5-8107-a2fd85229b21
-- title:
--   Lemma 15.9 (Fritz John, corrected): at a constrained minimizer w⋆ there are multipliers α₀ ≥ 0, αᵢ ≥ 0, not all zero, vanishing off the active set, with α₀∇f(w⋆) + ∑ αᵢ∇gᵢ(w⋆) = 0
-- statement:
--   **Lemma 15.9 (Fritz John)** (in its correct form). Suppose that $w^\star \in \operatorname{argmin}_w f(w)$ subject to $g_i(w) \le 0$ for all $i \in [m]$, where $f, g_1, \dots, g_m$ are differentiable, and let $I = \{i : g_i(w^\star) = 0\}$. Then there exist $\alpha_0 \ge 0$ and $\alpha \in \mathbb{R}^m$ with $\alpha_i \ge 0$, not all zero, $\alpha_i = 0$ for $i \notin I$, such that $\alpha_0\nabla f(w^\star) + \sum_{i \in I}\alpha_i\nabla g_i(w^\star) = 0$.
--
--   The book states the conclusion as $\nabla f(w^\star) + \sum_{i \in I}\alpha_i \nabla g_i(w^\star) = 0$ with $\alpha \in \mathbb{R}^m$; that version fails for $f(w) = w$, $g_1(w) = w^2$ on $\mathbb{R}$ ($w^\star = 0$, $\nabla f = 1$, $\nabla g_1(0) = 0$). For Theorem 15.8 the constraints are affine and $\alpha_0 = 1$ can be taken.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §15.3 p. 211, Lemma 15.9 (Fritz John), with the multiplier on ∇f restored; see the docstring

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 15.9 (Fritz John)** (p. 211), in its correct form. Suppose `w⋆ ∈ argmin_w f(w)`
subject to `gᵢ(w) ≤ 0` for `i ∈ [m]`, where `f, g₁, …, g_m` are differentiable, and let
`I = {i : gᵢ(w⋆) = 0}`. Then there exist multipliers `α₀ ≥ 0` and `α ∈ ℝ^m` with `αᵢ ≥ 0`, not all
zero, `αᵢ = 0` for `i ∉ I`, and `α₀ ∇f(w⋆) + ∑_{i ∈ I} αᵢ ∇gᵢ(w⋆) = 0`. The book prints the
conclusion without the multiplier `α₀` (and with `α` unrestricted in sign); that version fails
for `f(w) = w`, `g₁(w) = w²` on `ℝ`, where `w⋆ = 0`, `∇f = 1` and `∇g₁(0) = 0`. -/
theorem fritz_john {d m : ℕ} (f : Vec d → ℝ) (g : Fin m → Vec d → ℝ) (hf : Differentiable ℝ f)
    (hg : ∀ i, Differentiable ℝ (g i)) (wstar : Vec d) (hfeas : ∀ i, g i wstar ≤ 0)
    (hmin : ∀ w, (∀ i, g i w ≤ 0) → f wstar ≤ f w) :
    ∃ (α₀ : ℝ) (α : Fin m → ℝ), 0 ≤ α₀ ∧ (∀ i, 0 ≤ α i) ∧ (α₀ ≠ 0 ∨ ∃ i, α i ≠ 0) ∧
      (∀ i, g i wstar ≠ 0 → α i = 0) ∧
      α₀ • gradient f wstar + ∑ i, α i • gradient (g i) wstar = 0 := by sorry

end UnderstandingML
