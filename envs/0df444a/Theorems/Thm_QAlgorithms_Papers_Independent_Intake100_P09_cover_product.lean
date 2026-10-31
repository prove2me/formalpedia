-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P09_cover_product
-- name    : QAlgorithms.Papers.Independent.Intake100.P09.cover_product
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-30T12:49:39.372602+00:00
-- url     : https://prove2.me/theorems/06f4e846-4f0e-47fb-ba0e-fedb541c4366
-- title:
--   Products of covers are covers
-- statement:
--   Let $\tau$ be a cover pretopology on the category of smooth manifolds. Thus identity maps are covers, composites of covers are covers, and the smooth pullback of a cover along any smooth map exists and is again a cover. Let $Y,M,Y',M'$ be smooth manifolds and let $\pi:Y\to M$ and $\pi':Y'\to M'$ be $\tau$-covers. Then
--
--   $$
--   \pi\times\pi':Y\times Y'\longrightarrow M\times M',\qquad (y,y')\longmapsto(\pi(y),\pi'(y')),
--   $$
--
--   is a $\tau$-cover. This closure property is used for the degreewise nerve covers in Proposition 5.5.
--
--   **Formalization Note** Manifolds carry finite-dimensional real models, smooth atlases, and the usual Hausdorff and second countable structures, without boundary. The empty manifold is allowed. The product and product map use Mathlib's actual product atlases and smooth maps. Pullback universality quantifies over smooth mediating maps; no claim of existence of arbitrary manifold pullbacks is imposed.
-- source:
--   Equivariance In Higher Geometry, arXiv:1004.4558v4, PDF p. 24, Lemma 5.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P09

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Intake100.P09

open scoped Manifold ContDiff

/-- Lemma 5.6 (PDF p. 24): the product of any two tau-covers in Man is a
 tau-cover. The pretopology axioms are those fixed in Section 2.2, p. 9. -/
theorem cover_product (tau : CoverPretopology.{u})
    {Y M Yother Mother : SmoothManifold.{u}}
    (pi : SmoothMap Y M) (piOther : SmoothMap Yother Mother)
    (hpi : tau.covers pi) (hpiOther : tau.covers piOther) :
    tau.covers (smoothProductMap pi piOther) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P09

end
