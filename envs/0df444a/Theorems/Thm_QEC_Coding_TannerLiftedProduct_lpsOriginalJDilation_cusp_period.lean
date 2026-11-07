-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilation_cusp_period
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilation_cusp_period
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:07:35.221972+00:00
-- url     : https://prove2.me/theorems/378bd1e3-2ea2-4a4c-8c19-7af831cae405
-- title:
--   Tanner Lifted Product: lps Original JDilation cusp period
-- statement:
--   The actual original minimum cusp width is a strict period of the twice-translated SL group; used by genuine translated E4 and Delta cusp analyticity and q recovery.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L174-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L174-L182

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilation_cusp_period (N : ℕ) [NeZero N] (hN : 0<N) (ρ : SL(2,ℤ)) :
    (lpsOriginalCuspGroup N ρ).strictWidthInfty ∈
      (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹ •
        (ConjAct.toConjAct (lpsE2AffineMatrix N hN 0)⁻¹ •
          (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)))).strictPeriods := by sorry
