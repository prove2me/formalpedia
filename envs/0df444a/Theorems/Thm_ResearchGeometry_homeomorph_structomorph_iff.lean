-- Prove2me | Theorems.Thm_ResearchGeometry_homeomorph_structomorph_iff
-- name    : ResearchGeometry.homeomorph_structomorph_iff
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:33:19.894486+00:00
-- url     : https://prove2.me/theorems/9fdfa276-8e5a-4460-8199-6112338e0bfd
-- title:
--   A fixed homeomorphism admits groupoid compatibility exactly when both directions are differentiable
-- statement:
--   Let M and M′ be manifolds of order n over the same model with corners. For a specified homeomorphism e between them, there exists a structomorphism for the order-n differentiability groupoid with underlying homeomorphism exactly e if and only if e and its inverse are both differentiable to order n.
-- source:
--   Ryan Shin, unpublished Bridge.lean (2026), Structomorph.contMDiff, Structomorph.toDiffeomorph, Diffeomorph.toStructomorph, and structomorphEquivDiffeomorph; source SHA-256 e8ea6b66f6bd675ca272e862e0825ab2db1f8bb792eaffe1b9e8f5d89024d302. These targets are a newly authored theorem-valued interface to the existing checked constructions, not a verbatim split of the original project.

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Diffeomorph

open Set ChartedSpace
open scoped Manifold ContDiff Topology

namespace ResearchGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {n : ℕ∞ω} [hM : IsManifold I n M] [hM' : IsManifold I n M']

include hM hM'



theorem homeomorph_structomorph_iff (e : M ≃ₜ M') :
    (∃ h : Structomorph (contDiffGroupoid n I) M M', h.toHomeomorph = e) ↔
    ContMDiff I I n e ∧ ContMDiff I I n e.symm := by sorry



end ResearchGeometry
