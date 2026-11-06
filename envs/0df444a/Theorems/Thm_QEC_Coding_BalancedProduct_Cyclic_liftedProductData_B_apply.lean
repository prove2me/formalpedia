-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_B_apply
-- name    : QEC.Coding.BalancedProduct.Cyclic.liftedProductData_B_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:04:57.596536+00:00
-- url     : https://prove2.me/theorems/3b737139-3069-456e-80f9-f31b9ca1b56d
-- title:
--   Cyclic: lifted Product Data B apply
-- statement:
--   The Cyclic construction uses the lifted Product Data B apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L163-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L163-L167

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.Cyclic.liftedProductData_B_apply
    {G : Type u} {aRow aCol : Type v} [Group G]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (r c : Unit) :
    (liftedProductData A x).B r c = cyclicBoundaryElement x := by sorry

attribute [defeq] QEC.Coding.BalancedProduct.Cyclic.liftedProductData_B_apply
