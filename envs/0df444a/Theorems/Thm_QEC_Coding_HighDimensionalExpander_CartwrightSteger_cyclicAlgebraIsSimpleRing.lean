-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraIsSimpleRing
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraIsSimpleRing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:50:33.542453+00:00
-- url     : https://prove2.me/theorems/cf5d3901-eb23-4607-9425-4fad07592ba7
-- title:
--   Cartwright Steger: cyclic Algebra Is Simple Ring
-- statement:
--   The construction-owned cyclic division algebra is simple as a ring.
--   Together with `cyclicAlgebraIsCentral` and the explicit cyclic basis, this
--   supplies the finite-dimensional central-simple-algebra premises used by the
--   specialized strong-approximation argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicDivisionAlgebra.lean#L161-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicDivisionAlgebra.lean#L161-L164

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraIsSimpleRing
    (P : BasePrime) (r : Rank) : IsSimpleRing (CyclicAlgebra P r) := by sorry
