-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_groupObjectsInSmoothManifolds
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.groupObjectsInSmoothManifolds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:28:14.472768+00:00
-- url     : https://prove2.me/theorems/912a23a6-6789-47b5-9bd6-7160362dd7e0
-- title:
--   Smooth group objects are Lie groups
-- statement:
--   Let $G$ be an ordinary finite-dimensional real smooth manifold without boundary, using the Hausdorff and second countable convention, modeled on a finite-dimensional real normed vector space $E$. Fix multiplication $m$, identity $e$, and inverse $i$. These maps define a group object in smooth manifolds if and only if their computed group structure is a Lie group on the same manifold:
--
--   $$\text{group diagrams and smooth }m,i\quad\Longleftrightarrow\quad G\text{ is a }C^\infty\text{ Lie group with those operations}.$$
--
--   The identity map from the point manifold is automatically smooth. Dimension zero and the one-point group are included. The statement expresses the source's ordinary smooth-manifold correspondence and makes no claim about general locally convex Lie groups.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 3, §1 and footnote 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF p. 3, footnote 3: group objects in ordinary differentiable manifolds
are Lie groups. Both sides use the SAME finite-dimensional real smooth manifold
without boundary, with the usual Hausdorff and second countable conventions.
Dimension zero is included. -/
theorem groupObjectsInSmoothManifolds
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type u} [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace E G] [IsManifold (𝓘(ℝ, E)) ∞ G] (D : GroupMaps G) :
    SmoothGroupObject (E := E) D ↔
      ∃ h : GroupDiagrams D,
        letI : Group G := groupOfMaps D h
        LieGroup (𝓘(ℝ, E)) ∞ G := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
