-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleInputList_length
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleInputList_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:03:53.949678+00:00
-- url     : https://prove2.me/theorems/2f0cbaad-4137-4a55-9d91-c0fbbdfeac8a
-- title:
--   BDL26 Random Perturbation: triangle Input List length
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle Input List length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L13-L14
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L13-L14

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Mathlib.Data.List.FinRange
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.triangleInputList_length (P : TannerSquarePresentation) :
    (triangleInputList P).length = Fintype.card (Triangle P) := by sorry
