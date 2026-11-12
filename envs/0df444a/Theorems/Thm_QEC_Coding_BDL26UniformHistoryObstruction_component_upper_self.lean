-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_component_upper_self
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.component_upper_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:07:54.03728+00:00
-- url     : https://prove2.me/theorems/01ef4e85-1c05-4659-9c08-75f9eacec9a0
-- title:
--   BDL26 Uniform History Obstruction: component upper self
-- statement:
--   The BDL26 Uniform History Obstruction construction uses the component upper self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformComponentMask.lean#L95-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformComponentMask.lean#L95-L101

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformHistoryObstruction.component_upper_self (S : OddScale) (j : Nat) (lower : Finset (StrictLowerNode S j))
    (p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)))
    (hp : (upperSyndrome S j).val p ≠ 0) : p ∈ upperRegion S j (component S j lower p hp) := by sorry
