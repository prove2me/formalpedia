-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_markedAdjacent_iff
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.markedAdjacent_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:55:34.033733+00:00
-- url     : https://prove2.me/theorems/867b97ba-d3be-4c2f-8f47-5afd837a6e54
-- title:
--   BDL26 Canonical History Marks: marked Adjacent iff
-- statement:
--   The BDL26 Canonical History Marks construction uses the marked Adjacent iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L183-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L183-L184

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_markedAdjacent_iff
attribute [local simp] QEC.Coding.BDL26TopOwnerIsolation.markedAdjacent_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.markedAdjacent_iff (u v : Node S n) : markedAdjacent S n sigma u v ↔
    (decodingGraph S (n + 2)).adjacent u v ∧ u ∈ marks S n sigma ∧ v ∈ marks S n sigma := by sorry
