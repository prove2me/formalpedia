-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isArithVar_bot_4411830e09a7
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isArithVar_bot_4411830e09a7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:43.53583+00:00
-- url     : https://prove2.me/theorems/cb9549d7-d2d6-49c5-b2dc-880707347da2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Arith Var bot 4411830e09a7: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Arith Var bot 441183
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Arith Var bot 4411830e09a7 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Arith Var bot 4411830e09a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermFubiniStudyO1.lean#L168-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermFubiniStudyO1.lean#L168-L177

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isArithVar_bot_4411830e09a7 (n : ℕ) : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (n + 1)))) (n + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isArithVar_bot» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isArithVar_bot_4411830e09a7
