-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_eq_horizontalPart_add_verticalPart
-- name    : QEC.Coding.BalancedProduct.PKDistance.HammingWeight_eq_horizontalPart_add_verticalPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:58:52.675508+00:00
-- url     : https://prove2.me/theorems/ce8da37d-d4e2-480f-9f5d-5d3c90fae454
-- title:
--   PKDistance: Hamming Weight eq horizontal Part add vertical Part
-- statement:
--   The two concrete lifted-product blocks partition the physical qubits, so
--   their Hamming weights add exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L695-L707
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L695-L707

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w

theorem QEC.Coding.BalancedProduct.PKDistance.HammingWeight_eq_horizontalPart_add_verticalPart
    {G aRow aCol : Type}
    [Fintype G] [Fintype aRow] [Fintype aCol]
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G)) :
    HammingWeight z =
      HammingWeight (horizontalPart z) + HammingWeight (verticalPart z) := by sorry
