-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldCyclicBasis_apply
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldCyclicBasis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:57:41.085385+00:00
-- url     : https://prove2.me/theorems/18aaec06-30c7-4c81-85c6-4169494baca7
-- title:
--   Cartwright Steger: function Field Cyclic Basis apply
-- statement:
--   The Cartwright Steger construction uses the function Field Cyclic Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebraBasis.lean#L486-L491
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebraBasis.lean#L486-L491

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebraBasis
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldCyclicBasis_apply
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    functionFieldCyclicBasis P r p =
      functionFieldCyclicBasisVector P r p := by sorry
