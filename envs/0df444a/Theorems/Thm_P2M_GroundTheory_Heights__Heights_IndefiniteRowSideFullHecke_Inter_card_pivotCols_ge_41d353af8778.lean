-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_card_pivotCols_ge_41d353af8778
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_card_pivotCols_ge_41d353af8778
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:42.698139+00:00
-- url     : https://prove2.me/theorems/ddca4ae0-d943-4871-8861-e031e09f940c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter card pivot Cols ge 41d353af8778: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter card pivot Cols ge 41
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter card pivot Cols ge 41d353af8778 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter card pivot Cols ge 41d353af8778 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L13-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg
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
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_card_pivotCols_ge_41d353af8778 {n : ℕ} (a : Fin (n - 1)) :
    Fintype.card {b : Fin n // (a : ℕ) ≤ b} = n - a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«card_pivotCols_ge» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_card_pivotCols_ge_41d353af8778
