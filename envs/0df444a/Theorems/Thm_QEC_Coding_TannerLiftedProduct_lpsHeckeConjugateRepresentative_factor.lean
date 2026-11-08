-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateRepresentative_factor
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateRepresentative_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:04:18.553824+00:00
-- url     : https://prove2.me/theorems/70c81fd7-071a-418f-adf0-05e68b9ff060
-- title:
--   Tanner Lifted Product: lps Hecke Conjugate Representative factor
-- statement:
--   The second canonical inverse representative has its actual original real Hecke factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L38-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L38-L50

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateRepresentative_factor (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    ∃δ : SL(2,ℤ), δ∈CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩) * Matrix.SpecialLinearGroup.mapGL ℝ
        (lpsHeckeConjugateRepresentative N p hNp i : SL(2,ℤ))⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p i := by sorry
