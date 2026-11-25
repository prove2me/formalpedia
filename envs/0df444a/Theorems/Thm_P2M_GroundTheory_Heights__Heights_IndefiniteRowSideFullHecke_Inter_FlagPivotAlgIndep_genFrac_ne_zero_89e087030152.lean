-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotAlgIndep_genFrac_ne_zero_89e087030152
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotAlgIndep_genFrac_ne_zero_89e087030152
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:47.961851+00:00
-- url     : https://prove2.me/theorems/da93c974-98f4-4d27-b637-27aa86b87c8a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Alg Indep gen Frac ne zero 89e087030152: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Fl
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Alg Indep gen Frac ne zero 89e087030152 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Alg Indep gen Frac ne zero 89e087030152 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagPivotAlgIndep.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagPivotAlgIndep.lean#L18-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagPivotAlgIndep
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotAlgIndep
variable (F : Type) [Field F] (n : ℕ)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotAlgIndep_genFrac_ne_zero_89e087030152 (p : Fin n × Fin n) : genFrac F n p ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«FlagPivotAlgIndep».«genFrac_ne_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotAlgIndep_genFrac_ne_zero_89e087030152
