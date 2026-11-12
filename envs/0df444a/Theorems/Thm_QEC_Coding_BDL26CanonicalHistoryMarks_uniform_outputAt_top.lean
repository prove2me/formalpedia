-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_uniform_outputAt_top
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.uniform_outputAt_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:07:04.151085+00:00
-- url     : https://prove2.me/theorems/9c64186c-5427-4809-aedc-e171d0d10ec8
-- title:
--   BDL26 Canonical History Marks: uniform output At top
-- statement:
--   The BDL26 Canonical History Marks construction uses the uniform output At top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L107-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L107-L110

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26CanonicalHistoryMarks.uniform_outputAt_top (S : OddScale) (j : Nat) :
    outputAt S (2 * j + 2) (BDL26UniformHistoryObstruction.upperSyndrome S j)
      (Fin.last (2 * j + 1)) = BDL26UniformHistoryObstruction.topOutput S j := by sorry
