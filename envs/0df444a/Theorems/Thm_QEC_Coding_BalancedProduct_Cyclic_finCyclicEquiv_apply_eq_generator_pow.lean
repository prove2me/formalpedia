-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicEquiv_apply_eq_generator_pow
-- name    : QEC.Coding.BalancedProduct.Cyclic.finCyclicEquiv_apply_eq_generator_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:05:02.025216+00:00
-- url     : https://prove2.me/theorems/332c9c5f-fe17-468d-bc77-ba3f7281aa26
-- title:
--   Cyclic: fin Cyclic Equiv apply eq generator pow
-- statement:
--   The Cyclic construction uses the fin Cyclic Equiv apply eq generator pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L32-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L32-L41

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.Cyclic.finCyclicEquiv_apply_eq_generator_pow
    (q : Nat) [NeZero q] (k : Fin q) :
    finCyclicEquiv q k = cyclicGenerator q ^ k.val := by sorry
