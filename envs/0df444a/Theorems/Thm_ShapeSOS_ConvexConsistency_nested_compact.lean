-- Prove2me | Theorems.Thm_ShapeSOS_ConvexConsistency_nested_compact
-- name    : ShapeSOS.ConvexConsistency.nested_compact
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:21:59.923241+00:00
-- url     : https://prove2.me/theorems/4f9ea216-a05a-477e-bd46-cad554124e84
-- title:
--   Lemma B.9 — nested compact sets with singleton intersection shrink to that point
-- statement:
--   Let $x^*\in\mathbb R^n$ and let $(S_j)$ be nonempty compact sets with $S_{j+1}\subseteq S_j$ and $\bigcap_jS_j=\{x^*\}$. Then
--   $$\forall\epsilon>0\ \exists k_0\ \forall k\ge k_0,\qquad S_k\subseteq B(x^*,\epsilon).$$
--   Here the ball is open and uses Euclidean distance. This is the compactness statement used by Theorem B.8.
--
--   Differences from the source:
--   - encoding: real finite-dimensional coordinates and Euclidean geometry → Fin n → ℝ with its usual topology and explicit norm₂ = sqrt(sum x_i²); reason: the topology is the Euclidean topology and all numerical distances use the Euclidean norm
--   - encoding: sets indexed by 1,2,... → sets indexed by 0,1,...; reason: reindexing j by j+1 preserves every hypothesis and the eventual containment conclusion
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, p. 32, Lemma B.9

import Definitions.Def_ShapeSOS_ConvexConsistency_Geometry

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory

namespace ShapeSOS.ConvexConsistency

theorem nested_compact (n : ℕ) (xstar : Vec n) (S : ℕ → Set (Vec n))
    (hne : ∀ j, (S j).Nonempty) (hcomp : ∀ j, IsCompact (S j))
    (hmono : ∀ j, S (j+1) ⊆ S j) (hinter : (⋂ j, S j) = {xstar}) :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
      S k ⊆ {x | norm₂ (x-xstar) < ε} := by sorry

end ShapeSOS.ConvexConsistency
