-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_rawEventUniverse_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.rawEventUniverse_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:59:23.093767+00:00
-- url     : https://prove2.me/theorems/641fa736-11bf-4886-8e6d-ed151862009c
-- title:
--   BDL26 Random Perturbation: raw Event Universe cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the raw Event Universe cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventPreprocessingCost.lean#L11-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventPreprocessingCost.lean#L11-L26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPreprocessingCost
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.rawEventUniverse_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) :
    (rawEventUniverseQuery P J hr).2 ≤ rawUniverseBudget (Fintype.card (Triangle P)) := by sorry
