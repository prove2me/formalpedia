-- Prove2me | Theorems.Thm_PoincareFormalization_exists_smooth_structure_three
-- name    : PoincareFormalization.exists_smooth_structure_three
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-09T04:36:43.079175+00:00
-- url     : https://prove2.me/theorems/6445ec61-f49c-47ce-b681-7ab9ea9a4059
-- title:
--   Moise's theorem: every topological $3$-manifold admits a smooth structure
-- statement:
--   Let $M$ be a second countable Hausdorff topological space that is locally modelled on $\mathbb{R}^3$: it carries an atlas of charts, each a homeomorphism from an open subset of $M$ onto an open subset of $\mathbb{R}^3 =$ `EuclideanSpace ℝ (Fin 3)`. That is, $M$ is a topological $3$-manifold without boundary.
--
--   Then $M$ admits a smooth structure: there is an atlas on the *same* topological space $M$, again modelled on $\mathbb{R}^3$, all of whose transition maps are $C^\infty$.
--
--   This is the existence half of Moise's theorem, which gives every topological $3$-manifold an essentially unique piecewise linear structure and smooth structure; uniqueness is not asserted here. It is the step that lets a purely topological hypothesis be handed to Ricci flow, which evolves a Riemannian metric and so is defined only on a smooth manifold. Morgan and Tian record it in the footnote to their statement of the Poincare conjecture, as the reason why the topological and the smooth classification of $3$-manifolds are equivalent.
--
--   **Formalization note.** A term of type `ChartedSpace (EuclideanSpace ℝ (Fin 3)) M` is exactly an atlas on the fixed topological space $M$, so the existential quantifier ranges over the possible smooth structures on that topology; the ambient instance argument supplies the given topological atlas. The exhibited atlas is not required to be compatible with, or to refine, that given atlas — only the topology of $M$ is held fixed. The model with corners is `𝓡 3`, the identity model on $\mathbb{R}^3$, and the smoothness order is $\infty$. No compactness or connectedness is assumed.
-- source:
--   Edwin E. Moise, "Affine structures in 3-manifolds. V. The triangulation theorem and Hauptvermutung", Annals of Mathematics (2) 56 (1952), 96-114, doi:10.2307/1969769: any topological 3-manifold has an essentially unique piecewise-linear structure and smooth structure; only the existence of the smooth structure is asserted here. Stated in the form used here by John W. Morgan and Gang Tian, "Ricci Flow and the Poincare Conjecture", Clay Mathematics Monographs 3 (2007), Introduction, p. 5, footnote 1: "Every topological 3-manifold admits a differentiable structure and every homeomorphism between smooth 3-manifolds can be approximated by a diffeomorphism. Thus, classification results about topological 3-manifolds up to homeomorphism and about smooth 3-manifolds up to diffeomorphism are equivalent. In this book 'manifold' means 'smooth manifold.'" (https://arxiv.org/pdf/math/0607607, printed p. 5). See also John Milnor, "The Poincare Conjecture", Clay Mathematics Institute problem description, end of Section 3, p. 5: "In dimension 3, the discrepancies between topological, piecewise linear, and differentiable theories disappear" (https://www.claymath.org/wp-content/uploads/2022/06/poincare.pdf).

import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareFormalization

theorem exists_smooth_structure_three (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      @IsManifold ℝ _ _ _ _ _ _ (𝓡 3) ∞ M _ cs := by
  sorry

end PoincareFormalization
