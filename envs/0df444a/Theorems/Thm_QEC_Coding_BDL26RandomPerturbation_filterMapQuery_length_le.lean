-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_filterMapQuery_length_le
-- name    : QEC.Coding.BDL26RandomPerturbation.filterMapQuery_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:42:50.212431+00:00
-- url     : https://prove2.me/theorems/b9043b81-7211-4f35-a2a2-16c5796830d0
-- title:
--   BDL26 Random Perturbation: filter Map Query length le
-- statement:
--   The BDL26 Random Perturbation construction uses the filter Map Query length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedFilterMap.lean#L18-L21
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedFilterMap.lean#L18-L21

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.filterMapQuery_length_le {A B : Type*} (q : A → Option B × ℕ) (L : List A) :
    (filterMapQuery q L).1.length ≤ L.length := by sorry
