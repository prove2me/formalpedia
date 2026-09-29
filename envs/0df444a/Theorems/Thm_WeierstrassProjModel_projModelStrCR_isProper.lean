-- Prove2me | Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
-- name    : WeierstrassProjModel.projModelStrCR_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/8c62d7ee-da09-527a-b6cc-43b68a684f94
-- title:
--   Properness of the projective Weierstrass model over the base
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$ (an element of `WeierstrassCurve.Projective R`). Consider the $\mathbb{N}$-grading `projModelGradingCR V` on the ring `ProjModelRingCR V`, obtained by pushing the standard grading by total degree `homogeneousSubmodule (Fin 3) R` of the polynomial ring in three variables over $R$ forward to the quotient by the underlying ideal of the homogeneous ideal `projModelHomogeneousIdealCR V` attached to $V$, and the morphism `projModelStrCR V` from $\operatorname{Proj}$ of this graded ring to $\operatorname{Spec} R$ given by the canonical map $\operatorname{Proj} \to \operatorname{Spec}$ of the degree-zero part followed by $\operatorname{Spec}$ of the structure map $R \to (\mathrm{projModelGradingCR}\ V)_0$. The assertion is that this morphism satisfies Mathlib's predicate `AlgebraicGeometry.IsProper`. No hypotheses beyond commutativity of $R$ are imposed: $R$ need not be Noetherian or a domain, and $V$ is arbitrary, singular models included. Nothing about flatness, smoothness, fibre dimension or a group law is asserted.
--
--   This is the properness of the projective plane model $\operatorname{Proj}\big(R[X,Y,Z]/(W^{\mathrm{hom}})\big) \to \operatorname{Spec} R$ of a Weierstrass equation, specialising the properness of $\operatorname{Proj}$ of a graded ring generated in degree one over its degree-zero part. It is used wherever the projective model of a Weierstrass curve must be known proper over the base, for instance in the constructions of curves with quaternionic level structure and of relative group laws on such models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_projModelStrCR_isProper.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Proper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassProjModel.projModelStrCR_isProper {R : Type*} [CommRing R]
    (V : WeierstrassCurve.Projective R) :
    AlgebraicGeometry.IsProper (WeierstrassProjModel.projModelStrCR V) := by sorry
