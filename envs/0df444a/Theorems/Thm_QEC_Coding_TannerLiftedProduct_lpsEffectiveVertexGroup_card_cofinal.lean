-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveVertexGroup_card_cofinal
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveVertexGroup_card_cofinal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:18:19.861548+00:00
-- url     : https://prove2.me/theorems/546da05c-01e0-47d7-957b-f582c34c920c
-- title:
--   Tanner Lifted Product: lps Effective Vertex Group card cofinal
-- statement:
--   These computed-prime groups have unbounded cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L100-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L100-L108

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveVertexGroup_card_cofinal {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∀ N : ℕ, ∃ n, N ≤ Fintype.card (LPSEffectiveVertexGroup hp hp4 n) := by sorry
