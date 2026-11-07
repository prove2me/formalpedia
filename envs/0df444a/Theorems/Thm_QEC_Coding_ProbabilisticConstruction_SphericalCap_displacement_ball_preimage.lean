-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacement_ball_preimage
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.displacement_ball_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:04:49.706899+00:00
-- url     : https://prove2.me/theorems/11a0c018-d9bc-4ef9-9071-7ff237ca947c
-- title:
--   Spherical Cap: displacement ball preimage
-- statement:
--   The Spherical Cap construction uses the displacement ball preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/SmallCap.lean#L15-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/SmallCap.lean#L15-L25

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_SmallCap
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set Metric
open scoped ENNReal

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.displacement_ball_preimage {R ε : ℝ} (hR : 0 < R) (hε : 0 ≤ ε)
    (v : Sphere) :
    (fun s : Sphere => R • (s : Space)) ⁻¹' closedBall (R • (v : Space)) ε =
      cap v (1 - ε^2 / (2*R^2)) := by sorry
