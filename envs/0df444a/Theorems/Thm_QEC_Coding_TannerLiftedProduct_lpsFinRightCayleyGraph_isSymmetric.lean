-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFinRightCayleyGraph_isSymmetric
-- name    : QEC.Coding.TannerLiftedProduct.lpsFinRightCayleyGraph_isSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:41:46.183672+00:00
-- url     : https://prove2.me/theorems/77ebcd06-67a7-4d34-8a2b-f0c2061d86d7
-- title:
--   Tanner Lifted Product: lps Fin Right Cayley Graph is Symmetric
-- statement:
--   The reindexed concrete LPS Cayley multigraph remains symmetric.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L263-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L263-L269

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsFinRightCayleyGraph_isSymmetric
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ) :
    SmallSetExpansion.IsSymmetric
      (rightCayleyGraph (lpsFinQuaternionFamilyLabel hp hp4 hCount n)) := by sorry
