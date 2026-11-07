-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capDisplacementLaw_closedBall_le
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_closedBall_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:54:48.703342+00:00
-- url     : https://prove2.me/theorems/da8061e8-e470-408a-aeca-835acf8e3e00
-- title:
--   Spherical Cap: cap Displacement Law closed Ball le
-- statement:
--   The Spherical Cap construction uses the cap Displacement Law closed Ball le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/SmallCap.lean#L44-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/SmallCap.lean#L44-L56

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_SmallCap
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set Metric
open scoped ENNReal

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_closedBall_le {R c ε : ℝ} (hR : 0 < R)
    (u v : Sphere) (hc0 : -1 < c) (hc1 : c < 1)
    (hε : 0 ≤ ε) (hεR : ε ≤ 2*R) :
    capDisplacementLaw R u c (closedBall (R • (v : Space)) ε) ≤
      ENNReal.ofReal (ε^2 / (2*R^2*(1-c))) := by sorry
