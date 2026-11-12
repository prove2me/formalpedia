-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_markedNodes_only_z
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.markedNodes_only_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:02:45.797786+00:00
-- url     : https://prove2.me/theorems/7203d16a-c799-4999-9c20-e2be65f17f64
-- title:
--   BDL26 Uniform History Obstruction: marked Nodes only z
-- statement:
--   The BDL26 Uniform History Obstruction construction uses the marked Nodes only z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformComponentMask.lean#L38-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformComponentMask.lean#L38-L41

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformHistoryObstruction.markedNodes_only_z (S : OddScale) (j : Nat) (lower : Finset (StrictLowerNode S j)) :
    BDL26UniformTopOwnerIsolation.TopMarksAreZ S (2 * j + 3) (markedNodes S j lower) := by sorry
