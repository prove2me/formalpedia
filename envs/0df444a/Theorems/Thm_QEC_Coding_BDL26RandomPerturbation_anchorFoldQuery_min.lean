-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_anchorFoldQuery_min
-- name    : QEC.Coding.BDL26RandomPerturbation.anchorFoldQuery_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:55:46.290222+00:00
-- url     : https://prove2.me/theorems/85667584-b423-472d-9691-8903f70638c6
-- title:
--   BDL26 Random Perturbation: anchor Fold Query min
-- statement:
--   The BDL26 Random Perturbation construction uses the anchor Fold Query min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L53-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L53-L70

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.anchorFoldQuery_min (P : TannerSquarePresentation) (a : Triangle P) (L : List (Triangle P)) :
    ∀ t ∈ a::L, triangleKey P (anchorFoldQuery P a L).1 ≤ triangleKey P t := by sorry
