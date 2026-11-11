-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_rootComponent
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.mem_rootComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:27:37.670756+00:00
-- url     : https://prove2.me/theorems/d2f2a35d-e9c3-4d3c-ae5e-dcc17e894691
-- title:
--   BDL26 Canonical History Marks: mem root Component
-- statement:
--   The BDL26 Canonical History Marks construction uses the mem root Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L230-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L230-L233

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.mem_rootComponent (w : Node S n) : w ∈ rootComponent S n sigma ↔
    root S n ∈ marks S n sigma ∧ w ∈ marks S n sigma ∧
      Relation.ReflTransGen (markedAdjacent S n sigma) w (root S n) := by sorry
