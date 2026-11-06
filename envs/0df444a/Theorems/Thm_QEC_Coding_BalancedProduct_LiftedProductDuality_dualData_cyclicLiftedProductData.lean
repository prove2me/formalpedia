-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_cyclicLiftedProductData
-- name    : QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_cyclicLiftedProductData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:38:55.648951+00:00
-- url     : https://prove2.me/theorems/bbaea60d-a1b9-45ff-ad01-84726991587b
-- title:
--   Lifted Product Duality: dual Data cyclic Lifted Product Data
-- statement:
--   Dualizing a cyclic lifted product star-transposes the Tanner matrix and
--   reverses the orientation of the cyclic generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L102-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L102-L108

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v

theorem QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_cyclicLiftedProductData
    {G aRow aCol : Type u} [Group G]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    dualData (Cyclic.liftedProductData A x) =
      Cyclic.liftedProductData (LiftedProduct.starTranspose A) x⁻¹ := by sorry
