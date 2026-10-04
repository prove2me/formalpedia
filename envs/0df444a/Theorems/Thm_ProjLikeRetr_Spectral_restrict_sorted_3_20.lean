-- Prove2me | Theorems.Thm_ProjLikeRetr_Spectral_restrict_sorted_3_20
-- name    : ProjLikeRetr.Spectral.restrict_sorted_3_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:02:14.404435+00:00
-- url     : https://prove2.me/theorems/0cdc9fd1-b862-4546-839c-d4f8391cbe79
-- title:
--   (3.20), proof of Theorem 3.9, p. 14 — near $\bar x$, the distance to $\mathcal M \cap B(\bar x,\delta)$ is attained on sorted points
-- statement:
--   Let $\mathcal M \subseteq \mathbb R^n$ and $\bar x \in \mathcal M \cap \mathbb R^n_\downarrow$. Then there is $\delta_1 > 0$ such that for every $\delta \in (0, \delta_1]$ for which $\mathcal M \cap B(\bar x, \delta)$ is strongly locally symmetric (3.15), the following holds: for every $x \in \mathbb R^n_\downarrow \cap B(\bar x, \delta)$ and every $y \in \mathcal M \cap B(\bar x, \delta)$ there is $z \in \mathcal M \cap B(\bar x, \delta) \cap \mathbb R^n_\downarrow$ with
--   $$
--   \|z - x\| \le \|y - x\|.
--   $$
--   Since $\mathcal M \cap B(\bar x, \delta) \cap \mathbb R^n_\downarrow \subseteq \mathcal M \cap B(\bar x, \delta)$, this is the identity
--   $$
--   \min_{y \in \mathcal M \cap B(\bar x, \delta)} \|x - y\| = \min_{y \in \mathcal M \cap B(\bar x, \delta) \cap \mathbb R^n_\downarrow} \|x - y\| \qquad (3.20)
--   $$
--   of the paper, stated without real-valued minima (the infimum of the left side is matched point by point on the right side).
--
--   This is the step of the proof of Theorem 3.9 that combines strong local symmetry with Lemma 3.8; together with (3.19) it gives $P_{\mathcal M}(x) = P_{\mathcal M \cap \mathbb R^n_\downarrow}(x)$ near $\bar x$, (3.18).
--
--   **Formalization Note** In the paper $x = \lambda(X)$ with $\|x - \bar x\| \le \delta/2$; the statement here allows any sorted $x$ in the open ball $B(\bar x, \delta)$, which is the range in which the paper's argument (Lemma 3.8) applies. "$\delta$ small enough" is rendered as $\exists \delta_1 > 0,\ \forall \delta \in (0, \delta_1]$.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 14, §3.4, proof of Theorem 3.9, display (3.20) (derivation p. 15)

import Mathlib
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet

namespace ProjLikeRetr.Spectral

/-- (3.20), proof of Theorem 3.9, p. 14: for all small enough `δ > 0` at which `M` is strongly
locally symmetric around `x̄`, the distance from a sorted `x ∈ B(x̄, δ)` to `M ∩ B(x̄, δ)` is
not decreased by restricting to sorted points: every `y ∈ M ∩ B(x̄, δ)` is matched by a sorted
`z ∈ M ∩ B(x̄, δ)` at most as far from `x`. -/
theorem restrict_sorted_3_20 {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (xbar : EuclideanSpace ℝ (Fin n)) (hxbar : xbar ∈ M ∩ sortedDesc n) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → IsStronglyLocallySymmetric M xbar δ →
      ∀ x ∈ sortedDesc n, x ∈ Metric.ball xbar δ →
        ∀ y ∈ M ∩ Metric.ball xbar δ, ∃ z ∈ M ∩ Metric.ball xbar δ,
          z ∈ sortedDesc n ∧ ‖z - x‖ ≤ ‖y - x‖ := by sorry

end ProjLikeRetr.Spectral
