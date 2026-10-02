-- Prove2me | Theorems.Thm_ShorNonsmooth_RAlgorithm_width_dilation_lower_bound
-- name    : ShorNonsmooth.RAlgorithm.width_dilation_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:14:00.001014+00:00
-- url     : https://prove2.me/theorems/7775ae23-da2f-4e49-bd15-6bd06ed48711
-- title:
--   Lemma 3.3 — contracting along a long chord of $W$ keeps the width above $d(W)/\sqrt{1 + (1-\beta^2)/(\beta^2\gamma^2)}$
-- statement:
--   Let $W$ be a convex, closed and bounded body in $E_n$ ($n \ge 1$) with width $d(W)$, let $z_1, z_2 \in W$, let $0 < \beta \le 1$, and suppose that
--   $$
--   \gamma = \frac{\|z_1 - z_2\|}{d(W)} \ge 1 .
--   $$
--   Let $R_\beta(\xi)$ be the operator of space dilation in the direction $\xi$ with coefficient $\beta$. Then
--   $$
--   d\!\left(R_\beta\!\left(\frac{z_1 - z_2}{\|z_1 - z_2\|}\right) W\right) \ge \frac{d(W)}{\sqrt{1 + (1 - \beta^2)/(\beta^2 \gamma^2)}} .
--   $$
--
--   Contracting a convex body along the direction of one of its chords that is at least as long as the width cannot make the body much thinner: the loss is controlled by the ratio $\gamma$. This is the step that limits the shrinkage of the transformed almost-gradient sets in the $r$-algorithm.
--
--   **Formalization Note** The book states $\beta \le 1$; $\beta > 0$ is added because the bound divides by $\beta^2$ and the lemma is used with $\beta = 1/\alpha$, $\alpha > 1$. "Body" is taken to mean nonempty interior, so $d(W) > 0$ and $\gamma$ is defined.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 80–81, Lemma 3.3

import Mathlib
import Definitions.Def_ShorNonsmooth_RAlgorithm_Widths

open scoped InnerProductSpace

namespace ShorNonsmooth.RAlgorithm

/-- Shor (1985), pp. 80–81, **Lemma 3.3**. Let `W` be a convex, closed and bounded body in `E_n`,
`z₁, z₂ ∈ W`, `0 < β ≤ 1` (the book writes `β ≤ 1`; `β > 0` is implicit: the bound divides by
`β²` and the lemma is applied with `β = 1/α`, `α > 1`), and `γ = ‖z₁ - z₂‖ / d(W) ≥ 1`. Then
`d(R_β((z₁ - z₂)/‖z₁ - z₂‖) W) ≥ d(W) / √(1 + (1 - β²)/(β² γ²))`. -/
theorem width_dilation_lower_bound {n : ℕ} (hn : 0 < n) (W : Set (EuclideanSpace ℝ (Fin n)))
    (hW_convex : Convex ℝ W) (hW_closed : IsClosed W) (hW_bdd : Bornology.IsBounded W)
    (hW_body : (interior W).Nonempty)
    (z₁ z₂ : EuclideanSpace ℝ (Fin n)) (hz₁ : z₁ ∈ W) (hz₂ : z₂ ∈ W)
    (β : ℝ) (hβ_pos : 0 < β) (hβ_le : β ≤ 1)
    (γ : ℝ) (hγ : γ = ‖z₁ - z₂‖ / width W) (hγ_ge : 1 ≤ γ) :
    width W / Real.sqrt (1 + (1 - β ^ 2) / (β ^ 2 * γ ^ 2)) ≤
      width (dilation β (‖z₁ - z₂‖⁻¹ • (z₁ - z₂)) '' W) := by sorry

end ShorNonsmooth.RAlgorithm
