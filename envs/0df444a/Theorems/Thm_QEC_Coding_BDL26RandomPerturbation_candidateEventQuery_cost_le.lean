-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_candidateEventQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.candidateEventQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:31:31.281192+00:00
-- url     : https://prove2.me/theorems/9ccfd8a7-74e5-497e-bc6d-0c38254bc613
-- title:
--   BDL26 Random Perturbation: candidate Event Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the candidate Event Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibleListQuery.lean#L101-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibleListQuery.lean#L101-L106

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibilityQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibleListQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.candidateEventQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) (hL : L.length = 4) :
    (candidateEventQuery P J hr L).2 ≤ 100000*(Fintype.card (Triangle P)+1)^2+1 := by sorry
