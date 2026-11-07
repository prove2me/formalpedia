-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_orderedInsertQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.orderedInsertQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:52:26.003792+00:00
-- url     : https://prove2.me/theorems/4c7f939f-dc4e-425f-82c5-3153d1592a7f
-- title:
--   BDL26 Random Perturbation: ordered Insert Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the ordered Insert Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedLists.lean#L47-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedLists.lean#L47-L58

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.orderedInsertQuery_value {A : Type*} (cmp : A → A → Bool × ℕ)
    (r : A → A → Prop) [DecidableRel r]
    (hc : ∀ a b, (cmp a b).1 = true ↔ r a b) (a : A) (L : List A) :
    (orderedInsertQuery cmp a L).1 = L.orderedInsert r a := by sorry
