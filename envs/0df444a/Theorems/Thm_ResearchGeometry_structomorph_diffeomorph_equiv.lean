-- Prove2me | Theorems.Thm_ResearchGeometry_structomorph_diffeomorph_equiv
-- name    : ResearchGeometry.structomorph_diffeomorph_equiv
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:33:28.19682+00:00
-- url     : https://prove2.me/theorems/1ec519a5-a262-44d3-a497-0c58213b6c80
-- title:
--   Structomorphisms and diffeomorphisms are equivalent while preserving the underlying homeomorphism
-- statement:
--   For manifolds M and M′ of order n over one model with corners, there exists a bijection from the type of structomorphisms for the order-n differentiability groupoid to the type of order-n diffeomorphisms. For every structomorphism h, its image under this bijection has exactly the same underlying homeomorphism as h. The statement is a bijection of types, not a claim about topology on mapping spaces or categorical naturality.
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





theorem structomorph_diffeomorph_equiv :
    ∃ e : Structomorph (contDiffGroupoid n I) M M' ≃ (M ≃ₘ^n⟮I, I⟯ M'),
      ∀ h, (e h).toHomeomorph = h.toHomeomorph := by sorry

end ResearchGeometry
