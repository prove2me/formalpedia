-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsVertexGroup_card_cofinal
-- name    : QEC.Coding.TannerLiftedProduct.lpsVertexGroup_card_cofinal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:58:31.195034+00:00
-- url     : https://prove2.me/theorems/32d0f99b-c3bb-4db6-9b0a-c4650782f5a6
-- title:
--   Tanner Lifted Product: lps Vertex Group card cofinal
-- statement:
--   The `PSL(2,q)` vertex groups are cofinal in cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L133-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L133-L140

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsVertexGroup_card_cofinal
    (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∀ N : ℕ, ∃ n : ℕ,
      N ≤ Fintype.card (LPSVertexGroup hp hp4 n) := by sorry
