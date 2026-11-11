-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_inputAt_base
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.inputAt_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:02:17.406715+00:00
-- url     : https://prove2.me/theorems/d8edb5a8-a84c-48eb-86eb-84821576676e
-- title:
--   BDL26 Canonical History Marks: input At base
-- statement:
--   The BDL26 Canonical History Marks construction uses the input At base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L65-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L65-L71

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
variable (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.inputAt_base (B : RecursiveBaseLevelCorrection (Data S n))
    (he : CorrectionHistoryEntry.base B ∈ actualHistory S n sigma) :
    inputAt S n sigma 0 = B.input := by sorry
