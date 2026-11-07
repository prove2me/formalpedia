-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspQCoefficient_zero_add
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_zero_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:46:46.611698+00:00
-- url     : https://prove2.me/theorems/234e158c-3b4b-4852-b24e-3223492ff877
-- title:
--   Tanner Lifted Product: lps Original Cusp QCoefficient zero add
-- statement:
--   The actual removable coefficient at a cusp is additive in the original form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L239-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L239-L257

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_zero_add (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) : lpsOriginalCuspQCoefficient N (f+g) ρ 0=
      lpsOriginalCuspQCoefficient N f ρ 0+lpsOriginalCuspQCoefficient N g ρ 0 := by sorry
