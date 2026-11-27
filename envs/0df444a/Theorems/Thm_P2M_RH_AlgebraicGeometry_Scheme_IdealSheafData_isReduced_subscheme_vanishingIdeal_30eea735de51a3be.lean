-- Prove2me | Theorems.Thm_P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_30eea735de51a3be
-- name    : P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_30eea735de51a3be
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:29.117306+00:00
-- url     : https://prove2.me/theorems/32644701-bd50-4c13-bc6f-d4e59368578e
-- title:
--   P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data is Reduced subscheme vanishing Ideal 30eea735de51a3be: P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data is Reduced subscheme vanishing Ideal 30eea7
-- statement:
--   The P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data is Reduced subscheme vanishing Ideal 30eea735de51a3be construction uses the P2 M RH Algebraic Geometry Scheme Ideal Sheaf Data is Reduced subscheme vanishing Ideal 30eea735de51a3be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L414-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L414-L425

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

theorem P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_30eea735de51a3be
    (W : Scheme.{u}) (Z : TopologicalSpace.Closeds W) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by sorry

alias «AlgebraicGeometry».«Scheme».«IdealSheafData».«isReduced_subscheme_vanishingIdeal» := P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_30eea735de51a3be
