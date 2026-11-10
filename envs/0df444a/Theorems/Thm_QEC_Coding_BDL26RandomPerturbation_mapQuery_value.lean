-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_mapQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.mapQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:04:00.820662+00:00
-- url     : https://prove2.me/theorems/62317d33-bb37-4358-8880-dc2068fb99b5
-- title:
--   BDL26 Random Perturbation: map Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the map Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L34-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L34-L36

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Mathlib.Data.List.FinRange
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.mapQuery_value {A B : Type*} (q : A → B × ℕ) (L : List A) :
    (mapQuery q L).1 = L.map (fun a => (q a).1) := by sorry
