-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_sortQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.sortQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:38:26.843196+00:00
-- url     : https://prove2.me/theorems/7fb31982-b25a-4116-b4fd-c8cc85289561
-- title:
--   BDL26 Random Perturbation: sort Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the sort Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedLists.lean#L81-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedLists.lean#L81-L94

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.sortQuery_cost_le {A : Type*} (cmp : A → A → Bool × ℕ)
    (r : A → A → Prop) [DecidableRel r]
    (hv : ∀ a b, (cmp a b).1 = true ↔ r a b) (C : ℕ)
    (hc : ∀ a b, (cmp a b).2 ≤ C) (L : List A) :
    (sortQuery cmp L).2 ≤ (L.length+1)^2*(C+1) := by sorry
