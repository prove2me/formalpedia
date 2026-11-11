-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventUniverseQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.eventUniverseQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:57:28.232993+00:00
-- url     : https://prove2.me/theorems/305ca8c0-0983-4615-8898-ee482484f948
-- title:
--   BDL26 Random Perturbation: event Universe Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the event Universe Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventPreprocessingCost.lean#L31-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventPreprocessingCost.lean#L31-L58

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPreprocessingCost
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventUniverseQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) :
    (eventUniverseQuery P J hr).2 ≤ eventUniverseBudget (Fintype.card (Triangle P)) := by sorry
