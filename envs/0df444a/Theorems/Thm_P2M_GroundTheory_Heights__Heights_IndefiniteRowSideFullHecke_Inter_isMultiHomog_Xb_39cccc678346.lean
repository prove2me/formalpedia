-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isMultiHomog_Xb_39cccc678346
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isMultiHomog_Xb_39cccc678346
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:42.082026+00:00
-- url     : https://prove2.me/theorems/af1b6f68-a454-4e68-a99b-95031d95e20a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Multi Homog Xb 39cccc678346: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Multi Homog Xb 39cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Multi Homog Xb 39cccc678346 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Multi Homog Xb 39cccc678346 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermFubiniStudyO1.lean#L179-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermFubiniStudyO1.lean#L179-L185

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isMultiHomog_Xb_39cccc678346 (n : ℕ) (i : Fin n) : IsMultiHomog (Xb n i) fun _ => 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isMultiHomog_Xb» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isMultiHomog_Xb_39cccc678346
