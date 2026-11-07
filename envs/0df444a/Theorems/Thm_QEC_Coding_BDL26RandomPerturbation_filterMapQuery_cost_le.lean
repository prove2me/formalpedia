-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_filterMapQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.filterMapQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:43:21.302171+00:00
-- url     : https://prove2.me/theorems/a1131476-5927-4fe7-8509-49722c9bd4fe
-- title:
--   BDL26 Random Perturbation: filter Map Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the filter Map Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedFilterMap.lean#L23-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedFilterMap.lean#L23-L31

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.filterMapQuery_cost_le {A B : Type*} (q : A → Option B × ℕ) (L : List A) (C : ℕ)
    (hq : ∀ a ∈ L, (q a).2 ≤ C) : (filterMapQuery q L).2 ≤ L.length*(C+1) := by sorry
