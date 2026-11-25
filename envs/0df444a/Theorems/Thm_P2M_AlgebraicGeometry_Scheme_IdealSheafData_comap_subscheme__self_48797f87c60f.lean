-- Prove2me | Theorems.Thm_P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap_subscheme__self_48797f87c60f
-- name    : P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap_subscheme__self_48797f87c60f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:50.515021+00:00
-- url     : https://prove2.me/theorems/5a1041f1-3e80-5d60-b73c-1ca6408f2dce
-- title:
--   P2 M Algebraic Geometry Scheme Ideal Sheaf Data comap subscheme  self 48797f87c60f: P2 M Algebraic Geometry Scheme Ideal Sheaf Data comap subscheme  self 48797f87c60f
-- statement:
--   The P2 M Algebraic Geometry Scheme Ideal Sheaf Data comap subscheme  self 48797f87c60f construction uses the P2 M Algebraic Geometry Scheme Ideal Sheaf Data comap subscheme  self 48797f87c60f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L427-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L427-L431

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

theorem P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap_subscheme__self_48797f87c60f {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.comap I.subschemeι = ⊥ := by sorry

alias «AlgebraicGeometry».«Scheme».«IdealSheafData».«comap_subschemeι_self» := P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap_subscheme__self_48797f87c60f
