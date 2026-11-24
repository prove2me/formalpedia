-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_rename_prodMap_one_85d5f711b452
-- name    : P2M_GroundTheory_Heights__Heights_rename_prodMap_one_85d5f711b452
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:22.385941+00:00
-- url     : https://prove2.me/theorems/005a6d05-ea4b-4607-bf41-199df44d3e88
-- title:
--   P2 M Ground Theory Heights  Heights rename prod Map one 85d5f711b452: P2 M Ground Theory Heights  Heights rename prod Map one 85d5f711b452
-- statement:
--   The P2 M Ground Theory Heights  Heights rename prod Map one 85d5f711b452 construction uses the P2 M Ground Theory Heights  Heights rename prod Map one 85d5f711b452 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/RenameProdMapMul.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/RenameProdMapMul.lean#L31-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_rename_prodMap_one_85d5f711b452 (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map ⇑(1 : Equiv.Perm (Fin k)) id) p = p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«rename_prodMap_one» := P2M_GroundTheory_Heights__Heights_rename_prodMap_one_85d5f711b452
