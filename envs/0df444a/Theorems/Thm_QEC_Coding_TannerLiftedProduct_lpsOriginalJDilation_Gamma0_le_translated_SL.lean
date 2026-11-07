-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilation_Gamma0_le_translated_SL
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilation_Gamma0_le_translated_SL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:07:40.621991+00:00
-- url     : https://prove2.me/theorems/c60f2cb0-5290-4a79-9e9b-0ea0668c2efb
-- title:
--   Tanner Lifted Product: lps Original JDilation Gamma0 le translated SL
-- statement:
--   The original Gamma0(N) subgroup lies in the actual dilation-conjugated SL range, with membership proved from integral entries; used by all cusp subgroup inclusions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L145-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L145-L162

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilation_Gamma0_le_translated_SL (N : ℕ) (hN : 0<N) :
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (lpsE2AffineMatrix N hN 0)⁻¹ •
        (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by sorry
