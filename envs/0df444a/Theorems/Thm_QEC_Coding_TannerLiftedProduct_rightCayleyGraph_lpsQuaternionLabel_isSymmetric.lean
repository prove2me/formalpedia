-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightCayleyGraph_lpsQuaternionLabel_isSymmetric
-- name    : QEC.Coding.TannerLiftedProduct.rightCayleyGraph_lpsQuaternionLabel_isSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:41:45.969665+00:00
-- url     : https://prove2.me/theorems/45ce1454-2668-45fb-a23d-82aa2b0492c7
-- title:
--   Tanner Lifted Product: right Cayley Graph lps Quaternion Label is Symmetric
-- statement:
--   Inverse closure of the normalized quaternion labels makes the Cayley
--   multigraph symmetric for every admissible residue prime, independently of
--   the particular cofinal enumeration used below.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L201-L240
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L201-L240

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.rightCayleyGraph_lpsQuaternionLabel_isSymmetric
    (a : LPSResiduePrime p) :
    SmallSetExpansion.IsSymmetric
      (rightCayleyGraph (lpsQuaternionLabel a)) := by sorry
