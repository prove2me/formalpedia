-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lowerTriangleQuery_mem
-- name    : QEC.Coding.BDL26RandomPerturbation.lowerTriangleQuery_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:54:37.12189+00:00
-- url     : https://prove2.me/theorems/f52b01d2-c14e-4b50-8af1-3b1a60351fa7
-- title:
--   BDL26 Random Perturbation: lower Triangle Query mem
-- statement:
--   The BDL26 Random Perturbation construction uses the lower Triangle Query mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L20-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L20-L23

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.lowerTriangleQuery_mem (P : TannerSquarePresentation) (a b : Triangle P) :
    (lowerTriangleQuery P a b).1 = a ∨ (lowerTriangleQuery P a b).1 = b := by sorry
