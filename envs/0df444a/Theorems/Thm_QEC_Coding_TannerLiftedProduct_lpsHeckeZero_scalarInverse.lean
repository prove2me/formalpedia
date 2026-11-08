-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeZero_scalarInverse
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeZero_scalarInverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:05:01.788928+00:00
-- url     : https://prove2.me/theorems/7a970c27-a8dd-4495-850d-62e4e46cd35a
-- title:
--   Tanner Lifted Product: lps Hecke Zero scalar Inverse
-- statement:
--   The original zero finite matrix is exactly scalar(p) times the original infinity inverse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L53-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L53-L63

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeZero_scalarInverse (p : ℕ) [Fact p.Prime] :
    lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.mk0 (p:ℝ) (by exact_mod_cast (Fact.out:p.Prime).ne_zero)) *
          (lpsHeckeUpperGL ℝ p none)⁻¹ := by sorry
