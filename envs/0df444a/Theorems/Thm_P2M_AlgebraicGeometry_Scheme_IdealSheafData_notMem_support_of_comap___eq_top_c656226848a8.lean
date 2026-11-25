-- Prove2me | Theorems.Thm_P2M_AlgebraicGeometry_Scheme_IdealSheafData_notMem_support_of_comap___eq_top_c656226848a8
-- name    : P2M_AlgebraicGeometry_Scheme_IdealSheafData_notMem_support_of_comap___eq_top_c656226848a8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:19.787801+00:00
-- url     : https://prove2.me/theorems/6ae1969c-6b46-4037-8b1d-7733963dc193
-- title:
--   P2 M Algebraic Geometry Scheme Ideal Sheaf Data not Mem support of comap   eq top c656226848a8: P2 M Algebraic Geometry Scheme Ideal Sheaf Data not Mem support of comap   eq top c656226848a8
-- statement:
--   The P2 M Algebraic Geometry Scheme Ideal Sheaf Data not Mem support of comap   eq top c656226848a8 construction uses the P2 M Algebraic Geometry Scheme Ideal Sheaf Data not Mem support of comap   eq top c656226848a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L308-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L308-L316

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

theorem P2M_AlgebraicGeometry_Scheme_IdealSheafData_notMem_support_of_comap___eq_top_c656226848a8 (I : Y.IdealSheafData) {U : Y.Opens}
    (h : I.comap U.ι = ⊤) {x : Y} (hxU : x ∈ U) : x ∉ I.support := by sorry

alias «AlgebraicGeometry».«Scheme».«IdealSheafData».«notMem_support_of_comap_ι_eq_top» := P2M_AlgebraicGeometry_Scheme_IdealSheafData_notMem_support_of_comap___eq_top_c656226848a8
