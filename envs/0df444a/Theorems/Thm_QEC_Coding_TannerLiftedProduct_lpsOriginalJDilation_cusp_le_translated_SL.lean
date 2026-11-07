-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilation_cusp_le_translated_SL
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilation_cusp_le_translated_SL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:18:55.280936+00:00
-- url     : https://prove2.me/theorems/285b3cfe-df2d-4c89-bd29-7f25f5f77ddc
-- title:
--   Tanner Lifted Product: lps Original JDilation cusp le translated SL
-- statement:
--   Conjugating the proved original subgroup inclusion at each actual integral cusp representative gives the true translated group inclusion; used by its strict cusp period.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L165-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L165-L171

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilation_cusp_le_translated_SL (N : ℕ) (hN : 0<N) (ρ : SL(2,ℤ)) :
    lpsOriginalCuspGroup N ρ ≤
      ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹ •
        (ConjAct.toConjAct (lpsE2AffineMatrix N hN 0)⁻¹ •
          (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) := by sorry
