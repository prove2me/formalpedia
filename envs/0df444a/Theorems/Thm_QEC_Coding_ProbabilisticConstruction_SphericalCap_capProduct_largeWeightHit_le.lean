-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capProduct_largeWeightHit_le
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.capProduct_largeWeightHit_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:12:25.257653+00:00
-- url     : https://prove2.me/theorems/4be34a8e-c23f-49d5-bbe3-6d2b4f419bf2
-- title:
--   Spherical Cap: cap Product large Weight Hit le
-- statement:
--   The Spherical Cap construction uses the cap Product large Weight Hit le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleProduct.lean#L42-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleProduct.lean#L42-L56

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Mathlib.Probability.Independence.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.capProduct_largeWeightHit_le {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ)
    (u : Fin 3 → Sphere) (c : Fin 3 → ℝ) (hc0 : ∀ i, -1 < c i) (hc1 : ∀ i, c i < 1)
    (r : Fin 3 → Space) (z : Space) (i : Fin 3) :
    Measure.pi (fun j => capDisplacementLaw R (u j) (c j)) (largeWeightHit r z ρ i) ≤
      ENNReal.ofReal (6*ρ/(R*(1-c i))) := by sorry
