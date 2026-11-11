-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fourTuplesQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.fourTuplesQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:57:34.938713+00:00
-- url     : https://prove2.me/theorems/29f5a29a-67fb-48b8-89b2-8b331dce370c
-- title:
--   BDL26 Random Perturbation: four Tuples Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the four Tuples Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L86-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L86-L92

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.fourTuplesQuery_cost_le {A : Type*} (L : List A) :
    (fourTuplesQuery L).2 ≤ 13*L.length^4+L.length^3+L.length^2+L.length := by sorry
