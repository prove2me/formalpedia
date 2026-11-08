-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeZero_slashInverse
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeZero_slashInverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:03:44.349183+00:00
-- url     : https://prove2.me/theorems/fc756f52-c089-4e23-8bd4-47baa6864741
-- title:
--   Tanner Lifted Product: lps Hecke Zero slash Inverse
-- statement:
--   Actual scalar invariance identifies the original zero slash with infinity inverse slash.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L66-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L66-L69

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeZero_slashInverse (p : ℕ) [Fact p.Prime] (g : ℍ→ℂ) :
    (g ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩)) =
      (g ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) := by sorry
