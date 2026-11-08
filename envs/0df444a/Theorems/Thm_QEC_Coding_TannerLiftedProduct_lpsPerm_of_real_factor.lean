-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPerm_of_real_factor
-- name    : QEC.Coding.TannerLiftedProduct.lpsPerm_of_real_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:01:05.039194+00:00
-- url     : https://prove2.me/theorems/768b165b-7aab-4810-b77f-4763ee099674
-- title:
--   Tanner Lifted Product: lps Perm of real factor
-- statement:
--   An actual real GL factor identity induces the genuine permutation conjugacy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L49-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L49-L62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsPerm_of_real_factor (A : GL (Fin 2) ℝ) (γ δ : SL(2,ℤ))
    (he : A*Matrix.SpecialLinearGroup.mapGL ℝ γ=
      Matrix.SpecialLinearGroup.mapGL ℝ δ*A) :
    (MulAut.conj (MulAction.toPerm A : Equiv.Perm ℍ))
      (MulAction.toPerm γ : Equiv.Perm ℍ)=(MulAction.toPerm δ : Equiv.Perm ℍ) := by sorry
