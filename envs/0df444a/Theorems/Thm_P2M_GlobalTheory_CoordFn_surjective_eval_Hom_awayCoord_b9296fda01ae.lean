-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CoordFn_surjective_eval_Hom_awayCoord_b9296fda01ae
-- name    : P2M_GlobalTheory_CoordFn_surjective_eval_Hom_awayCoord_b9296fda01ae
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:43:27.380158+00:00
-- url     : https://prove2.me/theorems/cb9aee65-1058-5c7d-a4d7-530c7ff84697
-- title:
--   P2 M Global Theory Coord Fn surjective eval Hom away Coord b9296fda01ae: P2 M Global Theory Coord Fn surjective eval Hom away Coord b9296fda01ae
-- statement:
--   The P2 M Global Theory Coord Fn surjective eval Hom away Coord b9296fda01ae construction uses the P2 M Global Theory Coord Fn surjective eval Hom away Coord b9296fda01ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsIsoAppLEOfOpensRange.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsIsoAppLEOfOpensRange.lean#L48-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsIsoAppLEOfOpensRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
open GlobalTheory GlobalTheory.CoordFn

theorem P2M_GlobalTheory_CoordFn_surjective_eval_Hom_awayCoord_b9296fda01ae {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (i : Fin 3) :
    Function.Surjective (MvPolynomial.eval₂Hom (awayConst W i) (awayCoord W i)) := by sorry

alias «GlobalTheory».«CoordFn».«surjective_eval₂Hom_awayCoord» := P2M_GlobalTheory_CoordFn_surjective_eval_Hom_awayCoord_b9296fda01ae
