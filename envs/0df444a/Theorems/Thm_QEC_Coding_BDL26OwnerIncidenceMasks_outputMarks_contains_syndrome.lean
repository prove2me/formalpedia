-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_outputMarks_contains_syndrome
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.outputMarks_contains_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:03:53.009838+00:00
-- url     : https://prove2.me/theorems/5782880f-10f9-482a-9daf-542931d59175
-- title:
--   BDL26 Owner Incidence Masks: output Marks contains syndrome
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the output Marks contains syndrome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L87-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L87-L96

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26OwnerIncidenceMasks.outputMarks_contains_syndrome {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
    {V : Type} [Fintype V] [DecidableEq V]
    (O : AssemblyStepOutput D i) (synOwner : C2 i.succ → V)
    (pieceOwner : Fin O.localComponents.length → V)
    (p : C2 i.succ) (hp : O.input.val p ≠ 0) :
    synOwner p ∈ outputMarks O synOwner pieceOwner := by sorry
