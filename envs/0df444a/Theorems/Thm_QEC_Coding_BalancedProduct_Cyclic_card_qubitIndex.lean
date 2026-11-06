-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_card_qubitIndex
-- name    : QEC.Coding.BalancedProduct.Cyclic.card_qubitIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:05:56.242857+00:00
-- url     : https://prove2.me/theorems/a756fa12-3d7a-4b49-8b18-0cd97aff9e33
-- title:
--   Cyclic: card qubit Index
-- statement:
--   Exact qubit count before identifying the Tanner-orbit cardinalities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L186-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L186-L193

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Theorems.Thm_QEC_Coding_LiftedProduct_card_qubitIndex

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.Cyclic.card_qubitIndex
    {aRow aCol : Type} [Fintype aRow] [Fintype aCol]
    (q : Nat) [NeZero q] :
    Fintype.card
        (LiftedProduct.QubitIndex aRow aCol Unit Unit (CyclicGroup q)) =
      q * (Fintype.card aCol + Fintype.card aRow) := by sorry
