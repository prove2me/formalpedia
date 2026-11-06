-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicInvEquiv_apply_eq_invGenerator_pow
-- name    : QEC.Coding.BalancedProduct.Cyclic.finCyclicInvEquiv_apply_eq_invGenerator_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:05:20.806933+00:00
-- url     : https://prove2.me/theorems/3067910b-43e9-4784-9dcf-b8d05fc590af
-- title:
--   Cyclic: fin Cyclic Inv Equiv apply eq inv Generator pow
-- statement:
--   The Cyclic construction uses the fin Cyclic Inv Equiv apply eq inv Generator pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L48-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L48-L53

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.Cyclic.finCyclicInvEquiv_apply_eq_invGenerator_pow
    (q : Nat) [NeZero q] (k : Fin q) :
    finCyclicInvEquiv q k = (cyclicGenerator q)⁻¹ ^ k.val := by sorry
