-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_OrderSplitCartwrightStegerLattice_to_global
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_OrderSplitCartwrightStegerLattice_to_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:50:47.771137+00:00
-- url     : https://prove2.me/theorems/73b0200d-36fb-4e87-87f9-dc4cc790c3dc
-- title:
--   Cartwright Steger: map Order Split Cartwright Steger Lattice to global
-- statement:
--   Base change recovers the original global Cartwright--Steger matrix
--   group exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L780-L798
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L780-L798

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_OrderSplitCartwrightStegerLattice_to_global
    (P : BasePrime) (r : Rank) :
    (OrderSplitCartwrightStegerLattice P r).map
        (orderSplitBaseChangeGLHom P r) =
      CartwrightStegerMatrixGroup P r := by sorry
