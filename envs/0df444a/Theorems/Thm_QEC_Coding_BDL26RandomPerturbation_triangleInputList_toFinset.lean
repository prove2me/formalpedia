-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleInputList_toFinset
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleInputList_toFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:13:16.201843+00:00
-- url     : https://prove2.me/theorems/5d6158bb-744f-4735-8c26-f8b9f89d1a1a
-- title:
--   BDL26 Random Perturbation: triangle Input List to Finset
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle Input List to Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ColorQuery.lean#L56-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ColorQuery.lean#L56-L63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare

theorem QEC.Coding.BDL26RandomPerturbation.triangleInputList_toFinset (P : TannerSquarePresentation) :
    (triangleInputList P).toFinset = Finset.univ := by sorry
