-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventToMaster_scan_priority
-- name    : QEC.Coding.BDL26RandomPerturbation.eventToMaster_scan_priority
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:01:20.081861+00:00
-- url     : https://prove2.me/theorems/2c0a59f0-1ee3-4de2-b9c7-c86a3df2b328
-- title:
--   BDL26 Random Perturbation: event To Master scan priority
-- statement:
--   The scan compares sorted triangle keys, rather than inherited subset order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L61-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L61-L64

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.eventToMaster_scan_priority (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) :
    (masterEventOrder P).toLE.le (eventToMaster P J r e) (eventToMaster P J r f) ↔
      (geometricEventOrder P J r).toLE.le e f := by sorry
