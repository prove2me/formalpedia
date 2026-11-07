-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_sortQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.sortQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:52:51.255149+00:00
-- url     : https://prove2.me/theorems/983d9fec-b352-45b1-a496-e41c3c4f8ba7
-- title:
--   BDL26 Random Perturbation: sort Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the sort Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedLists.lean#L60-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedLists.lean#L60-L68

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.sortQuery_value {A : Type*} (cmp : A → A → Bool × ℕ)
    (r : A → A → Prop) [DecidableRel r]
    (hc : ∀ a b, (cmp a b).1 = true ↔ r a b) (L : List A) :
    (sortQuery cmp L).1 = L.insertionSort r := by sorry
