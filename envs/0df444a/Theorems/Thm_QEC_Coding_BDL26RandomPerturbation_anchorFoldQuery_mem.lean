-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_anchorFoldQuery_mem
-- name    : QEC.Coding.BDL26RandomPerturbation.anchorFoldQuery_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:55:35.293229+00:00
-- url     : https://prove2.me/theorems/ea1ea4f8-c683-429f-9c5d-960e82508ec6
-- title:
--   BDL26 Random Perturbation: anchor Fold Query mem
-- statement:
--   The BDL26 Random Perturbation construction uses the anchor Fold Query mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L40-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L40-L51

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.anchorFoldQuery_mem (P : TannerSquarePresentation) (a : Triangle P) (L : List (Triangle P)) :
    (anchorFoldQuery P a L).1 ∈ a::L := by sorry
