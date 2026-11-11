-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixReadout_above
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.prefixReadout_above
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:51:59.848107+00:00
-- url     : https://prove2.me/theorems/ebb46dfb-5020-443b-ad2e-f5ae4089bd5a
-- title:
--   BDL26 History Syndrome Sensitivity: prefix Readout above
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the prefix Readout above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L141-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L141-L155

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
universe u
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.prefixReadout_above (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (B : AuditedBaseDecoder D) (n : Nat) (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩)
    (a : LevelIndex depth) (ha : n < a.val) :
    historyInputReadout D (prefixHistory D S B n hn sigma) a = 0 := by sorry
