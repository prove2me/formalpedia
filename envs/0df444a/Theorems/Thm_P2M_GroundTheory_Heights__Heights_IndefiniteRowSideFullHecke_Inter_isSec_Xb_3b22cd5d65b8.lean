-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_Xb_3b22cd5d65b8
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_Xb_3b22cd5d65b8
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:45.136025+00:00
-- url     : https://prove2.me/theorems/a4401cc1-84dc-4656-8c20-ef083d00dc9a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Sec Xb 3b22cd5d65b8: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Sec Xb 3b22cd5d65b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Sec Xb 3b22cd5d65b8 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Sec Xb 3b22cd5d65b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermFubiniStudyO1.lean#L195-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermFubiniStudyO1.lean#L195-L197

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_Xb_3b22cd5d65b8 (n : ℕ) (i : Fin (n + 1)) : IsSec (⊥ : Ideal (MRing (GlobalTheory (n + 1)))) (fsO1 (n + 1)) (Xb (n + 1) i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isSec_Xb» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_Xb_3b22cd5d65b8
