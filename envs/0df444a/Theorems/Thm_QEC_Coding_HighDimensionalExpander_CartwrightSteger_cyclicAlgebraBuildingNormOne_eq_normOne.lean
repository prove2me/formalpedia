-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraBuildingNormOne_eq_normOne
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraBuildingNormOne_eq_normOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:54:12.944732+00:00
-- url     : https://prove2.me/theorems/f7c0cce6-c002-4b61-9586-c380235115d4
-- title:
--   Cartwright Steger: cyclic Algebra Building Norm One eq norm One
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra Building Norm One eq norm One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/NormOneCompatibility.lean#L46-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/NormOneCompatibility.lean#L46-L73

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_SplitCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraBuildingNormOne_eq_normOne
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraBuildingNormOne P r = CyclicAlgebraNormOne P r := by sorry
