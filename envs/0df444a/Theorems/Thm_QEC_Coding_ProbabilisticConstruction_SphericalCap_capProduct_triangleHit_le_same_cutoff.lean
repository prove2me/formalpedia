-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capProduct_triangleHit_le_same_cutoff
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.capProduct_triangleHit_le_same_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:41:08.403338+00:00
-- url     : https://prove2.me/theorems/1d891b9b-0fbf-4d97-bf18-81a6b26c94c2
-- title:
--   Spherical Cap: cap Product triangle Hit le same cutoff
-- statement:
--   The Spherical Cap construction uses the cap Product triangle Hit le same cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleProduct.lean#L109-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleProduct.lean#L109-L119

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Mathlib.Probability.Independence.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.capProduct_triangleHit_le_same_cutoff {R ρ c : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ)
    (u : Fin 3 → Sphere) (hc0 : -1 < c) (hc1 : c < 1)
    (r : Fin 3 → Space) (z : Space) :
    Measure.pi (fun j => capDisplacementLaw R (u j) c) (triangleHit r z ρ) ≤
      ENNReal.ofReal (18*ρ/(R*(1-c))) := by sorry
