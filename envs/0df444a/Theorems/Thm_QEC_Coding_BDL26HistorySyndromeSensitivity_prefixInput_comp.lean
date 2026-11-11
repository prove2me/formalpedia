-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixInput_comp
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.prefixInput_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:45:39.552729+00:00
-- url     : https://prove2.me/theorems/a30ebc2c-bcbd-4748-ad4c-994ef5828668
-- title:
--   BDL26 History Syndrome Sensitivity: prefix Input comp
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the prefix Input comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L202-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L202-L226

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
universe u
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.prefixInput_comp (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (n : Nat) (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩)
    (b a : LevelIndex depth) (hb : b.val ≤ n) (ha : a.val ≤ b.val) :
    prefixInput D S n hn sigma a (ha.trans hb) =
      prefixInput D S b.val (by omega) (prefixInput D S n hn sigma b hb) a ha := by sorry
