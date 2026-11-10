-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_anchorFoldQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.anchorFoldQuery_cost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:55:50.843964+00:00
-- url     : https://prove2.me/theorems/43802bc3-5cba-4c7c-b111-256d8d9774df
-- title:
--   BDL26 Random Perturbation: anchor Fold Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the anchor Fold Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L72-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L72-L80

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.anchorFoldQuery_cost_le (P : TannerSquarePresentation) (a : Triangle P) (L : List (Triangle P)) :
    (anchorFoldQuery P a L).2 ≤ L.length*(2*Fintype.card (Triangle P)+2) := by sorry
