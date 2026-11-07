-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_indexQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.indexQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:38:08.065454+00:00
-- url     : https://prove2.me/theorems/7c459d42-adcb-4c95-9d4a-aeff1d310212
-- title:
--   BDL26 Random Perturbation: index Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the index Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedLists.lean#L15-L22
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedLists.lean#L15-L22

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.indexQuery_value {A : Type*} [DecidableEq A] [BEq A] [LawfulBEq A] (a : A) (L : List A) :
    (indexQuery a L).1 = L.idxOf a := by sorry
