-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fourTuple1Query_value
-- name    : QEC.Coding.BDL26RandomPerturbation.fourTuple1Query_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:13:28.017187+00:00
-- url     : https://prove2.me/theorems/922cf456-9ff4-4bb8-9c86-3bd568cd323a
-- title:
--   BDL26 Random Perturbation: four Tuple1 Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the four Tuple1 Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L40-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L40-L42

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.fourTuple1Query_value {A : Type*} (L : List A) (a b c : A) :
    (fourTuple1Query L a b c).1 = L.map (fun d => [a,b,c,d]) := by sorry
