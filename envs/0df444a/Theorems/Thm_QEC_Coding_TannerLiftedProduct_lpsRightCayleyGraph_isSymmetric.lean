-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRightCayleyGraph_isSymmetric
-- name    : QEC.Coding.TannerLiftedProduct.lpsRightCayleyGraph_isSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:41:08.870108+00:00
-- url     : https://prove2.me/theorems/0fd8fc86-0d5d-4e2b-8acc-0728c617b083
-- title:
--   Tanner Lifted Product: lps Right Cayley Graph is Symmetric
-- statement:
--   Inverse closure of the normalized quaternion labels makes the concrete
--   base Cayley multigraph symmetric.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L244-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L244-L249

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsRightCayleyGraph_isSymmetric
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    SmallSetExpansion.IsSymmetric
      (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) := by sorry
