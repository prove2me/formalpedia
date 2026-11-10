-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eligiblePairQuery_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.eligiblePairQuery_correct
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:15:43.479855+00:00
-- url     : https://prove2.me/theorems/56eedca3-3ffe-46c9-9c52-d42dcfa250df
-- title:
--   BDL26 Random Perturbation: eligible Pair Query correct
-- statement:
--   The BDL26 Random Perturbation construction uses the eligible Pair Query correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L104-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L104-L108

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibilityQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.eligiblePairQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (a b : Triangle P) :
    (eligiblePairQuery P J r a b).1 = true ↔
      triangleColor P a = triangleColor P b ∧ dist (oldAnchor P J a) (oldAnchor P J b) ≤ r := by sorry
