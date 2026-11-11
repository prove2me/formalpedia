-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fourTuple3Query_length
-- name    : QEC.Coding.BDL26RandomPerturbation.fourTuple3Query_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:57:22.840198+00:00
-- url     : https://prove2.me/theorems/93989a16-8500-4603-9296-9c1b3662066f
-- title:
--   BDL26 Random Perturbation: four Tuple3 Query length
-- statement:
--   The BDL26 Random Perturbation construction uses the four Tuple3 Query length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L54-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L54-L58

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.fourTuple3Query_length {A : Type*} (L : List A) (a : A) :
    (fourTuple3Query L a).1.length = L.length^3 := by sorry
