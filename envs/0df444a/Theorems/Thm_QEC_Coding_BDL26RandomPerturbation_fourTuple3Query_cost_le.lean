-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fourTuple3Query_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.fourTuple3Query_cost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:57:34.718868+00:00
-- url     : https://prove2.me/theorems/3e8cb595-16c0-4812-b451-2679956f59f6
-- title:
--   BDL26 Random Perturbation: four Tuple3 Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the four Tuple3 Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L78-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L78-L84

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.fourTuple3Query_cost_le {A : Type*} (L : List A) (a : A) :
    (fourTuple3Query L a).2 ≤ 12*L.length^3+L.length^2+L.length := by sorry
