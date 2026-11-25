-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_noCommonZero_one_32569d64e5bc
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_noCommonZero_one_32569d64e5bc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:47.75513+00:00
-- url     : https://prove2.me/theorems/fdae76aa-d193-4fe3-9cd9-b26e0e3ad9e1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set no Common Zero one 32569d64e5bc: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set no Common
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set no Common Zero one 32569d64e5bc construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set no Common Zero one 32569d64e5bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSaturatedFirstCoordinateLine.lean#L215-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSaturatedFirstCoordinateLine.lean#L215-L232

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open NumberField

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_noCommonZero_one_32569d64e5bc :
    NoCommonZero (mCoordIdeal (ι := PBlk 1) yPt) yPt (fsLine 1).a ![(1 : ℚ)] := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«noCommonZero_one» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_noCommonZero_one_32569d64e5bc
