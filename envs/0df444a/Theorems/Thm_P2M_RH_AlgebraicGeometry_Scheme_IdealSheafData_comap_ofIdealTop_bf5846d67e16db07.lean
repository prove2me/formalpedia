-- Prove2me | Theorems.Thm_P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop_bf5846d67e16db07
-- name    : P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop_bf5846d67e16db07
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:17.471953+00:00
-- url     : https://prove2.me/theorems/db79195c-224a-421c-b988-3f823a2d5b8c
-- title:
--   P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data comap of Ideal Top bf5846d67e16db07: P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data comap of Ideal Top bf5846d67e16db07
-- statement:
--   The P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data comap of Ideal Top bf5846d67e16db07 construction uses the P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data comap of Ideal Top bf5846d67e16db07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L187-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L187-L192

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}

theorem P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop_bf5846d67e16db07 [IsAffine X] [IsAffine Y] (J : Ideal Γ(Y, ⊤)) (f : X ⟶ Y) :
    (ofIdealTop J).comap f = ofIdealTop (J.map f.appTop.hom) := by sorry

alias «AlgebraicGeometry».«Scheme».«IdealSheafData».«comap_ofIdealTop» := P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop_bf5846d67e16db07
