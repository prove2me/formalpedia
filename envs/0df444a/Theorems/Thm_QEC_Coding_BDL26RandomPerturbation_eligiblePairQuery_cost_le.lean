-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eligiblePairQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.eligiblePairQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:02:04.165262+00:00
-- url     : https://prove2.me/theorems/b7a3e236-c0e9-4b51-994f-91a0cee630cc
-- title:
--   BDL26 Random Perturbation: eligible Pair Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the eligible Pair Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L110-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L110-L116

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibilityQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.eligiblePairQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (a b : Triangle P) :
    (eligiblePairQuery P J r a b).2 ≤ 6*Fintype.card (Triangle P)*(Fintype.card (Triangle P)+6)+2007 := by sorry
