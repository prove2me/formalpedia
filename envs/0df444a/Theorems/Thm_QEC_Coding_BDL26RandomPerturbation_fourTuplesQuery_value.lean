-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fourTuplesQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.fourTuplesQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:08:16.016718+00:00
-- url     : https://prove2.me/theorems/6c707ea9-42e5-4d43-8a2b-cc2cf4d6264f
-- title:
--   BDL26 Random Perturbation: four Tuples Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the four Tuples Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L60-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L60-L62

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.fourTuplesQuery_value {A : Type*} (L : List A) : (fourTuplesQuery L).1 = fourTuples L := by sorry
