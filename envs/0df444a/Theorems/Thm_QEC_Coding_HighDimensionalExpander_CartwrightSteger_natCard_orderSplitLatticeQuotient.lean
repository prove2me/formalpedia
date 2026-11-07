-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_orderSplitLatticeQuotient
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_orderSplitLatticeQuotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:50:46.973067+00:00
-- url     : https://prove2.me/theorems/42f2bdb7-e03f-458a-8a84-4ad79b7fa651
-- title:
--   Cartwright Steger: nat Card order Split Lattice Quotient
-- statement:
--   Exact vertex-count identity for the congruence quotient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L903-L909
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L903-L909

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_orderSplitLatticeQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (OrderSplitCartwrightStegerLattice P r ⧸
          OrderSplitCartwrightStegerCongruenceSubgroup P r level) =
      Nat.card (IndexCartwrightStegerImage P r level) := by sorry
