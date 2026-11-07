-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capHeight_difference
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.capHeight_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:31.763375+00:00
-- url     : https://prove2.me/theorems/97dee43f-d452-48a7-96ec-1f29804702dc
-- title:
--   Spherical Cap: cap Height difference
-- statement:
--   The Spherical Cap construction uses the cap Height difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Zones.lean#L58-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Zones.lean#L58-L61

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.capHeight_difference {a b : ℝ} (hab : a ≤ b) :
    capHeight a - capHeight b = max 0 (min 1 b - max (-1) a) := by sorry
