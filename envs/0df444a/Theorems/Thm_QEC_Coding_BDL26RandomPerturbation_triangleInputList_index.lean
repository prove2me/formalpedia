-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleInputList_index
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleInputList_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:05:21.941356+00:00
-- url     : https://prove2.me/theorems/8aa6af27-29ed-4259-9228-ab1f164b33c7
-- title:
--   BDL26 Random Perturbation: triangle Input List index
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle Input List index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L16-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L16-L27

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Mathlib.Data.List.FinRange
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.triangleInputList_index (P : TannerSquarePresentation) (t : Triangle P) :
    (triangleInputList P).idxOf t = triangleKey P t := by sorry
