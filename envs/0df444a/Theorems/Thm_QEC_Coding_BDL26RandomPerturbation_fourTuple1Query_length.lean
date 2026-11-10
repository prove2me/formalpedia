-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fourTuple1Query_length
-- name    : QEC.Coding.BDL26RandomPerturbation.fourTuple1Query_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:12:40.453208+00:00
-- url     : https://prove2.me/theorems/78f8e9c9-b80b-4f51-9ffd-9d2f5c49b482
-- title:
--   BDL26 Random Perturbation: four Tuple1 Query length
-- statement:
--   The BDL26 Random Perturbation construction uses the four Tuple1 Query length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L44-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L44-L46

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.fourTuple1Query_length {A : Type*} (L : List A) (a b c : A) :
    (fourTuple1Query L a b c).1.length = L.length := by sorry
