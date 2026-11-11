-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eligibleListQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.eligibleListQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:30:59.074663+00:00
-- url     : https://prove2.me/theorems/03cb44b0-4465-409e-abb1-cc262c8da4ea
-- title:
--   BDL26 Random Perturbation: eligible List Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the eligible List Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibleListQuery.lean#L49-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibleListQuery.lean#L49-L71

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibilityQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibleListQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eligibleListQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (L : List (Triangle P)) (hL : L.length = 4) :
    (eligibleListQuery P J r L).2 ≤ 100000*(Fintype.card (Triangle P)+1)^2 := by sorry
