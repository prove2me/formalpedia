-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_flatMapQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.flatMapQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:05:38.495999+00:00
-- url     : https://prove2.me/theorems/b0d2647c-cc26-470e-a44a-27256b362ee7
-- title:
--   BDL26 Random Perturbation: flat Map Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the flat Map Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L12-L14
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L12-L14

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.flatMapQuery_value {A B : Type*} (q : A → List B × ℕ) (L : List A) :
    (flatMapQuery q L).1 = L.flatMap (fun a => (q a).1) := by sorry
