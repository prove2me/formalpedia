-- Prove2me | Theorems.Thm_P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul_690258dfc4cf6c74
-- name    : P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul_690258dfc4cf6c74
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:10:25.413775+00:00
-- url     : https://prove2.me/theorems/ea115464-a09e-505f-b7ab-b7246cf69179
-- title:
--   P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data of Ideal Top mul 690258dfc4cf6c74: P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data of Ideal Top mul 690258dfc4cf6c74
-- statement:
--   The P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data of Ideal Top mul 690258dfc4cf6c74 construction uses the P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data of Ideal Top mul 690258dfc4cf6c74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L249-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L249-L252

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

theorem P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul_690258dfc4cf6c74 [IsAffine X] (I J : Ideal Γ(X, ⊤)) :
    ofIdealTop (I * J) = ofIdealTop I * ofIdealTop J := by sorry

alias «AlgebraicGeometry».«Scheme».«IdealSheafData».«ofIdealTop_mul» := P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul_690258dfc4cf6c74
