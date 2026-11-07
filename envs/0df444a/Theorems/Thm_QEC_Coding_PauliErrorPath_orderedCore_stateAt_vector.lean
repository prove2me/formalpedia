-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_orderedCore_stateAt_vector
-- name    : QEC.Coding.PauliErrorPath.orderedCore_stateAt_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:17:00.356091+00:00
-- url     : https://prove2.me/theorems/36810518-d335-44e0-bb41-1ec0b6693bc1
-- title:
--   Pauli Error Path: ordered Core state At vector
-- statement:
--   The Pauli Error Path construction uses the ordered Core state At vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L115-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L115-L126

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.PauliErrorPath

theorem QEC.Coding.PauliErrorPath.orderedCore_stateAt_vector
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup)
    (n : Nat) :
    ((orderedCore Q sites hnodup).stateAt n).vector =
      (Locality.restrictBinaryTo (sites.take n).toFinset Q).vector := by sorry
