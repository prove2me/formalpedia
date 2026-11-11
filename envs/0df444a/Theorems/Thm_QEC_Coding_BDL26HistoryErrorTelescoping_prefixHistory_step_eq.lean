-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_prefixHistory_step_eq
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.prefixHistory_step_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:13:35.479233+00:00
-- url     : https://prove2.me/theorems/c6e9fec3-d159-4613-87a9-5ff5f07614a8
-- title:
--   BDL26 History Error Telescoping: prefix History step eq
-- statement:
--   The BDL26 History Error Telescoping construction uses the prefix History step eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L304-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L304-L310

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.BDL26HistoryErrorTelescoping.prefixHistory_step_eq (D : BDL26DecoderData depth C0 C1 C2)
    (st : AlternatingStepData D) (B : AuditedBaseDecoder D)
    (i : StepIndex depth) (s : D.family.Syndrome i.succ) :
    prefixHistory D st B (i.val+1) (Nat.succ_le_of_lt i.isLt) s =
      .step i (st.step i s) ::
        prefixHistory D st B i.val (Nat.le_of_lt i.isLt) (st.step i s).coarse := by sorry
