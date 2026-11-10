-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_mapQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.mapQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:04:13.73288+00:00
-- url     : https://prove2.me/theorems/bc7be1d7-f84d-47b1-bc18-63d006e1bf17
-- title:
--   BDL26 Random Perturbation: map Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the map Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L38-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L38-L46

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Mathlib.Data.List.FinRange
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.mapQuery_cost_le {A B : Type*} (q : A → B × ℕ) (L : List A) (C : ℕ)
    (hq : ∀ a ∈ L, (q a).2 ≤ C) : (mapQuery q L).2 ≤ L.length*(C+1) := by sorry
