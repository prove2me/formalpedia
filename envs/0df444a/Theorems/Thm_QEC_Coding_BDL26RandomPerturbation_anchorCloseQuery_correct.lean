-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_anchorCloseQuery_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.anchorCloseQuery_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:15:15.806756+00:00
-- url     : https://prove2.me/theorems/7f2c1ffe-ff60-4a4d-bb91-ea9978152721
-- title:
--   BDL26 Random Perturbation: anchor Close Query correct
-- statement:
--   The BDL26 Random Perturbation construction uses the anchor Close Query correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L67-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L67-L86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibilityQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.anchorCloseQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    {radius : ℝ} (hr : 0 ≤ radius) (a b : Triangle P) :
    (anchorCloseQuery P J radius a b).1 = true ↔
      dist (oldAnchor P J a) (oldAnchor P J b) ≤ radius := by sorry
