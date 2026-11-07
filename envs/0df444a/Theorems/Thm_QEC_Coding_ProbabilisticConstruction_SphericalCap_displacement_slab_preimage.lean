-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacement_slab_preimage
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.displacement_slab_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:59.600414+00:00
-- url     : https://prove2.me/theorems/810071a5-b90e-4c41-a9dd-154d2b71f877
-- title:
--   Spherical Cap: displacement slab preimage
-- statement:
--   The Spherical Cap construction uses the displacement slab preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Slab.lean#L34-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Slab.lean#L34-L45

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.displacement_slab_preimage {R : ℝ} (hR : 0 < R) (n : Sphere) (d h : ℝ) :
    (fun s : Sphere => R • (s : Space)) ⁻¹' slab n d h =
      zone n ((d-h)/R) ((d+h)/R) := by sorry
