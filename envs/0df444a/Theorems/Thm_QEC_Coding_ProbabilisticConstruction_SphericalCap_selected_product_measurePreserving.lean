-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_selected_product_measurePreserving
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.selected_product_measurePreserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:12:06.297741+00:00
-- url     : https://prove2.me/theorems/24f5eb3f-bc93-47ac-b29b-7519c01cc883
-- title:
--   Spherical Cap: selected product measure Preserving
-- statement:
--   The Spherical Cap construction uses the selected product measure Preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleProduct.lean#L81-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleProduct.lean#L81-L90

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Mathlib.Probability.Independence.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.selected_product_measurePreserving {ι : Type*} [Fintype ι]
    (μ : ι → Measure Space) [∀ i, IsProbabilityMeasure (μ i)]
    (j : Fin 3 → ι) (hj : Function.Injective j) :
    MeasurePreserving (fun p : ι → Space => fun k => p (j k))
      (Measure.pi μ) (Measure.pi fun k => μ (j k)) := by sorry
