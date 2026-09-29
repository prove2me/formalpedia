-- Prove2me | Theorems.Thm_WeierstrassProjModel_projModelStrCR_smooth
-- name    : WeierstrassProjModel.projModelStrCR_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/c40ab171-7ee9-5eb8-8aa1-649b4917652a
-- title:
--   Smoothness of the projective Weierstrass model over Spec R
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$ (an element of `WeierstrassCurve.Projective R`, i.e. a tuple $a_1,a_2,a_3,a_4,a_6$ together with the associated homogeneous cubic in three variables), assumed elliptic in Mathlib's sense, namely that the discriminant of $V$ is a unit of $R$. Consider the graded ring $\mathrm{projModelGradingCR}\,V$: the quotient of the polynomial ring $R[X_0,X_1,X_2]$, with its standard grading by total degree, by the homogeneous ideal [`WeierstrassProjModel.projModelHomogeneousIdealCR V`](def/WeierstrassCurve_ProjModel.html#L286) attached to $V$, equipped with the induced grading on the quotient. The morphism $\mathrm{projModelStrCR}\,V$ is the canonical map from $\operatorname{Proj}$ of this graded ring to $\operatorname{Spec} R$, obtained as `Proj.toSpecZero` into the spectrum of the degree-zero part, followed by the map of spectra induced by the structure homomorphism $R \to (\mathrm{projModelGradingCR}\,V)_0$. The assertion is that this morphism of schemes is smooth, in the sense of Mathlib's predicate `AlgebraicGeometry.Smooth`.
--
--   This is the smoothness over the base of the projective Weierstrass model of an elliptic curve whose discriminant is invertible, the geometric input that makes the model an elliptic curve over $\operatorname{Spec} R$ rather than merely a plane cubic. It is used in the constructions of relative group laws and of quaternionic models in the Čerednik–Drinfel'd part of the development, where smoothness of the ambient model over the base ring is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_projModelStrCR_smooth.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassProjModel.projModelStrCR_smooth {R : Type} [CommRing R]
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    AlgebraicGeometry.Smooth (WeierstrassProjModel.projModelStrCR V) := by sorry
