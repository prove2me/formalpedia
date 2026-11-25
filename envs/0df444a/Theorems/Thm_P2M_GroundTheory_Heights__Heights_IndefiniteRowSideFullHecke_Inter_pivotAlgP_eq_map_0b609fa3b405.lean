-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotAlgP_eq_map_0b609fa3b405
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotAlgP_eq_map_0b609fa3b405
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:57.906504+00:00
-- url     : https://prove2.me/theorems/fdd24192-6170-4c34-b495-6c9505db4a6b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Alg P eq map 0b609fa3b405: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Alg P eq map 0b
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Alg P eq map 0b609fa3b405 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Alg P eq map 0b609fa3b405 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L69-L71

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
variable (F : Type) [Field F] (n : ℕ)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotAlgP_eq_map_0b609fa3b405 : pivotAlgP F n = (pivotAlg F n).map (flagMinorAlg F n).val := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«pivotAlgP_eq_map» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotAlgP_eq_map_0b609fa3b405
