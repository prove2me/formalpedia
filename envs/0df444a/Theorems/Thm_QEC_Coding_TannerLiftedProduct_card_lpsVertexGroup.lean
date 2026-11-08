-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsVertexGroup
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsVertexGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:58:40.550138+00:00
-- url     : https://prove2.me/theorems/877423af-62fe-4877-b595-f9798d18aba1
-- title:
--   Tanner Lifted Product: card lps Vertex Group
-- statement:
--   Exact order of the `n`th vertex group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L108-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L108-L113

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsVertexGroup
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    Fintype.card (LPSVertexGroup hp hp4 n) =
      let q := (lpsResiduePrimeSequence hp hp4 n).q
      q * (q ^ 2 - 1) / 2 := by sorry
