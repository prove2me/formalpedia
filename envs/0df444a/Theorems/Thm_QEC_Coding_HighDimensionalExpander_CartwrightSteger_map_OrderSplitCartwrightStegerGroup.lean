-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_OrderSplitCartwrightStegerGroup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_OrderSplitCartwrightStegerGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:50:38.95633+00:00
-- url     : https://prove2.me/theorems/1cca1e82-1ae7-45d4-a5d7-a95ded68cc30
-- title:
--   Cartwright Steger: map Order Split Cartwright Steger Group
-- statement:
--   The complete finite Cartwright--Steger image is the projective reduction
--   of the subgroup generated over the actual localized coefficient ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L913-L928
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L913-L928

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_OrderSplitCartwrightStegerGroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderSplitCartwrightStegerGroup P r).map
        (orderSplitReductionPGLHom P r level) =
      IndexCartwrightStegerImage P r level := by sorry
