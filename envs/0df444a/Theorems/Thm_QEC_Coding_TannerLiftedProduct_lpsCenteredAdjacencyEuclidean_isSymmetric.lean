-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredAdjacencyEuclidean_isSymmetric
-- name    : QEC.Coding.TannerLiftedProduct.lpsCenteredAdjacencyEuclidean_isSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:50:55.940347+00:00
-- url     : https://prove2.me/theorems/28b4548e-e2d5-4e28-87d2-9d529b07f293
-- title:
--   Tanner Lifted Product: lps Centered Adjacency Euclidean is Symmetric
-- statement:
--   The centered adjacency underlying the Euclidean LPS Hecke operators is
--   self-adjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L41-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L41-L49

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsCenteredAdjacencyEuclidean_isSymmetric
    (a : LPSResiduePrime p) :
    (SmallSetExpansion.centeredAdjacencyEuclidean
      (rightCayleyGraph (lpsQuaternionLabel a))
      (Fintype.card (LPSGeneratorIndex p))).IsSymmetric := by sorry
