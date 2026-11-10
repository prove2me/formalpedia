-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_anchorCloseQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.anchorCloseQuery_cost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:01:02.728947+00:00
-- url     : https://prove2.me/theorems/03d65151-34a2-47c8-b73d-f395e3048925
-- title:
--   BDL26 Random Perturbation: anchor Close Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the anchor Close Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L90-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L90-L96

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibilityQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.anchorCloseQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (a b : Triangle P) : (anchorCloseQuery P J radius a b).2 ≤ 2000 := by sorry
