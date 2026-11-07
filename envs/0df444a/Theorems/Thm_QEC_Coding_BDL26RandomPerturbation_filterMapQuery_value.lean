-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_filterMapQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.filterMapQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:11.987192+00:00
-- url     : https://prove2.me/theorems/81fb3221-9c15-4564-b91b-3ec68b97cf78
-- title:
--   BDL26 Random Perturbation: filter Map Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the filter Map Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedFilterMap.lean#L11-L16
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedFilterMap.lean#L11-L16

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.filterMapQuery_value {A B : Type*} (q : A → Option B × ℕ) (L : List A) :
    (filterMapQuery q L).1 = L.filterMap (fun a => (q a).1) := by sorry
