-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_flatMapQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.flatMapQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:07:28.048245+00:00
-- url     : https://prove2.me/theorems/72443b68-03ac-44f6-950d-9b1abaaae258
-- title:
--   BDL26 Random Perturbation: flat Map Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the flat Map Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L16-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean#L16-L26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.flatMapQuery_cost_le {A T : Type*} (q : A → List T × ℕ) (L : List A) (maxLength maxCost : ℕ)
    (hlen : ∀ a ∈ L, (q a).1.length ≤ maxLength) (hcost : ∀ a ∈ L, (q a).2 ≤ maxCost) :
    (flatMapQuery q L).2 ≤ L.length*(maxLength+maxCost+1) := by sorry
