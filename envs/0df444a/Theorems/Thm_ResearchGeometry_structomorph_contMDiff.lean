-- Prove2me | Theorems.Thm_ResearchGeometry_structomorph_contMDiff
-- name    : ResearchGeometry.structomorph_contMDiff
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:33:10.461258+00:00
-- url     : https://prove2.me/theorems/b87fabbf-5a10-4787-8818-ba6a1fd67df2
-- title:
--   Structomorphisms are differentiable
-- statement:
--   For manifolds of order n over the same model with corners, the homeomorphism underlying a structomorphism for the order-n differentiability groupoid is differentiable to order n.
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

theorem structomorph_contMDiff (h : Structomorph (contDiffGroupoid n I) M M') :
    ContMDiff I I n h.toHomeomorph := by sorry





end ResearchGeometry
