-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleLabelEqQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleLabelEqQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:00:34.03969+00:00
-- url     : https://prove2.me/theorems/903e3065-5ed1-4de5-9eec-8e04c77b25a0
-- title:
--   BDL26 Random Perturbation: triangle Label Eq Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle Label Eq Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L22-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L22-L29

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibilityQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.triangleLabelEqQuery_cost_le (P : TannerSquarePresentation) (a b : Triangle P) :
    (triangleLabelEqQuery P a b).2 ≤ 2*Fintype.card (Triangle P)+1 := by sorry
