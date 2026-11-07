-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_selected_capProduct_triangleHit_le
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.selected_capProduct_triangleHit_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:41:04.937901+00:00
-- url     : https://prove2.me/theorems/2a1d7d8d-6726-4c97-a54c-8296d3e7b1b0
-- title:
--   Spherical Cap: selected cap Product triangle Hit le
-- statement:
--   The Spherical Cap construction uses the selected cap Product triangle Hit le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleProduct.lean#L92-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleProduct.lean#L92-L107

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Mathlib.Probability.Independence.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.selected_capProduct_triangleHit_le {ι : Type*} [Fintype ι]
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ)
    (u : ι → Sphere) (c : ι → ℝ) (hc0 : ∀ i, -1 < c i) (hc1 : ∀ i, c i < 1)
    (j : Fin 3 → ι) (hj : Function.Injective j) (r : Fin 3 → Space) (z : Space) :
    Measure.pi (fun k => capDisplacementLaw R (u k) (c k))
      {p | (fun k => p (j k)) ∈ triangleHit r z ρ} ≤
      ENNReal.ofReal ((6*ρ/R) * ∑ k, 1/(1-c (j k))) := by sorry
