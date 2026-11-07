-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_cap_opposite_inter
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.cap_opposite_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:10:29.128165+00:00
-- url     : https://prove2.me/theorems/f18dafe6-33a8-4040-868d-39eb1efbe5b7
-- title:
--   Spherical Cap: cap opposite inter
-- statement:
--   The Spherical Cap construction uses the cap opposite inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L97-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L97-L106

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.cap_opposite_inter (u : Sphere) (c : ℝ) :
    cap u c ∩ cap (opposite u) (-c) =
      {s : Sphere | inner ℝ (u : Space) (s : Space) = c} := by sorry
