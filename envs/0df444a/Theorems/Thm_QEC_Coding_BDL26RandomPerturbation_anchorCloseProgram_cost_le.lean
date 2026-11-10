-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_anchorCloseProgram_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.anchorCloseProgram_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:15:32.422198+00:00
-- url     : https://prove2.me/theorems/aab2c8ed-8ae4-4ee5-85ad-9fa2d0f7f7bd
-- title:
--   BDL26 Random Perturbation: anchor Close Program cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the anchor Close Program cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L88-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L88-L88

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibilityQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.anchorCloseProgram_cost_le : anchorCloseProgram.cost ≤ 1000 := by sorry
