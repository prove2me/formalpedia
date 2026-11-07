-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitCartwrightStegerClassGeneratorGL_to_global
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderSplitCartwrightStegerClassGeneratorGL_to_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:49:30.124745+00:00
-- url     : https://prove2.me/theorems/becfc9d5-678e-410d-9b4a-63af23c15ca3
-- title:
--   Cartwright Steger: map order Split Cartwright Steger Class Generator GL to global
-- statement:
--   Base change identifies the class-indexed integral generator with the
--   original global Cartwright--Steger generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L729-L738
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L729-L738

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderSplitCartwrightStegerClassGeneratorGL_to_global
    (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    orderSplitBaseChangeGLHom P r
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u)) =
      cartwrightStegerGenerator P r u := by sorry
