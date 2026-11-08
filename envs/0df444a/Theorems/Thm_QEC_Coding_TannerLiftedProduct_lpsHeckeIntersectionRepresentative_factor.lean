-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersectionRepresentative_factor
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionRepresentative_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:02:24.874192+00:00
-- url     : https://prove2.me/theorems/f117c037-5f5b-4d82-8797-691e76526a0e
-- title:
--   Tanner Lifted Product: lps Hecke Intersection Representative factor
-- statement:
--   The first canonical inverse representative has its genuine original real Hecke factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L24-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L24-L35

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionRepresentative_factor (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    ∃δ : SL(2,ℤ), δ∈CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ
        (lpsHeckeIntersectionRepresentative N p hNp i : SL(2,ℤ))⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p i := by sorry
