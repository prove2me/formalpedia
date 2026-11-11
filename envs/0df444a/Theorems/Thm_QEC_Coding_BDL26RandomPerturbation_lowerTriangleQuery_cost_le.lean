-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lowerTriangleQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.lowerTriangleQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:55:19.679717+00:00
-- url     : https://prove2.me/theorems/e012ee58-ac12-46e0-a46b-b3dc5476a89c
-- title:
--   BDL26 Random Perturbation: lower Triangle Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the lower Triangle Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L25-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L25-L31

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.lowerTriangleQuery_cost_le (P : TannerSquarePresentation) (a b : Triangle P) :
    (lowerTriangleQuery P a b).2 ≤ 2*Fintype.card (Triangle P)+1 := by sorry
