-- Prove2me | Theorems.Thm_P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul_ffd4b47c5064b9ee
-- name    : P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul_ffd4b47c5064b9ee
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:07.031805+00:00
-- url     : https://prove2.me/theorems/0b2fb184-cf01-4d73-98f1-0e94cf5ed9bd
-- title:
--   P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data comap mul ffd4b47c5064b9ee: P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data comap mul ffd4b47c5064b9ee
-- statement:
--   The P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data comap mul ffd4b47c5064b9ee construction uses the P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data comap mul ffd4b47c5064b9ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L254-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L254-L273

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

theorem P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul_ffd4b47c5064b9ee (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by sorry

alias «AlgebraicGeometry».«Scheme».«IdealSheafData».«comap_mul» := P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul_ffd4b47c5064b9ee
