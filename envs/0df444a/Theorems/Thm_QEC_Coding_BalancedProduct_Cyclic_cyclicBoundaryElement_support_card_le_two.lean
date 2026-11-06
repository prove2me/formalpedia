-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_cyclicBoundaryElement_support_card_le_two
-- name    : QEC.Coding.BalancedProduct.Cyclic.cyclicBoundaryElement_support_card_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:32:11.124292+00:00
-- url     : https://prove2.me/theorems/72b07654-08fd-4d44-b995-b688cca6db00
-- title:
--   Cyclic: cyclic Boundary Element support card le two
-- statement:
--   The Cyclic construction uses the cyclic Boundary Element support card le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L75-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L75-L82

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.Cyclic.cyclicBoundaryElement_support_card_le_two
    {G : Type u} [Group G] [DecidableEq G] (x : G) :
    (cyclicBoundaryElement x).coeff.support.card ≤ 2 := by sorry
