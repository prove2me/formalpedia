-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_lemma_4_3
-- name    : TwoItemMenu1393.Main.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:35.813197+00:00
-- url     : https://prove2.me/theorems/3b4a6cf7-d917-4ad1-a097-f801d61ad0d9
-- title:
--   Lemma 4.3 — A nearby vertex from allocation variation
-- statement:
--   Let $S$ be a nonempty finite set of arbitrary affine functions on $\mathbb R^2$. Let $v_1,v_2,v_3$ form a nondegenerate equilateral triangle of side length $\ell>0$, and choose at each sample a gradient of a full-dimensional maximum cell containing that sample. If their affine interpolation $\Gamma$ satisfies
--   $$\|D\Gamma-I\|<1/10,$$
--   then the actual planar subdivision of the maximum has a vertex within distance $100\ell$ of the sample centroid. Samples may lie at ties and cells may be unbounded; no allocation or price restrictions are placed on these affine functions. This converts two-dimensional allocation variation into a nearby geometric vertex.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
--   - encoding: a finite maximum of affine functions and a nondegenerate triangle → a nonempty finite set of slope-intercept pairs and positive common side length; reason: duplicates do not affect the maximum; positivity is exactly nondegeneracy
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Lemma 4.3, p. 12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=12

import Definitions.Def_TwoItemMenu1393_Main_Subdivision
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Lemma 4.3, p. 12.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem lemma_4_3 (S : Finset Entry) (hS : S.Nonempty)
    (T G : Triangle) (ℓ : ℝ) (hT : equilateral T ℓ) (hG : FullCellSample S T G)
    (hJ : ‖interpolationJ T G - ContinuousLinearMap.id ℝ Vec‖ < 1/10) :
    ∃ v ∈ subdivisionVertices S, dist v ((1/3 : ℝ) • (T 0 + T 1 + T 2)) ≤ 100*ℓ := by sorry

end TwoItemMenu1393.Main
