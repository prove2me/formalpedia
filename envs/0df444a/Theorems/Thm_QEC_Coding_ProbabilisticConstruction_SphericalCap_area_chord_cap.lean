-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_chord_cap
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.area_chord_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:04:58.656856+00:00
-- url     : https://prove2.me/theorems/6bf84cae-6346-4b73-89fe-908286eb3bad
-- title:
--   Spherical Cap: area chord cap
-- statement:
--   The Spherical Cap construction uses the area chord cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/SmallCap.lean#L27-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/SmallCap.lean#L27-L42

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_SmallCap
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set Metric
open scoped ENNReal

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.area_chord_cap {R ε : ℝ} (hR : 0 < R) (hε : 0 ≤ ε)
    (hεR : ε ≤ 2*R) (v : Sphere) :
    area (cap v (1-ε^2/(2*R^2))) = ENNReal.ofReal (Real.pi*ε^2/R^2) := by sorry
