-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_eventBad
-- name    : QEC.Coding.BDL26RandomPerturbation.measurableSet_eventBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:00:17.244206+00:00
-- url     : https://prove2.me/theorems/8897f70b-a985-482a-bed8-a3d7c24c4a1c
-- title:
--   BDL26 Random Perturbation: measurable Set event Bad
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable Set event Bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Events.lean#L98-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Events.lean#L98-L105

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.measurableSet_eventBad (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius) :
    MeasurableSet (eventBad P J radius lambda K e) := by sorry
