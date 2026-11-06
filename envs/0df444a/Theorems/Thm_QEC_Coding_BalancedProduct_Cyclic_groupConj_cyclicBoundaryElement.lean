-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_groupConj_cyclicBoundaryElement
-- name    : QEC.Coding.BalancedProduct.Cyclic.groupConj_cyclicBoundaryElement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:06:24.072869+00:00
-- url     : https://prove2.me/theorems/15309252-c1c8-49dd-8cfb-17e80863f399
-- title:
--   Cyclic: group Conj cyclic Boundary Element
-- statement:
--   Star-conjugating the oriented cyclic boundary reverses its generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L85-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L85-L126

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.Cyclic.groupConj_cyclicBoundaryElement
    {G : Type u} [Group G] (x : G) :
    LiftedProduct.groupConj (cyclicBoundaryElement x) =
      cyclicBoundaryElement x⁻¹ := by sorry
