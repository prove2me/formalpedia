-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorMatrix_pow_matrixRank
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorMatrix_pow_matrixRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:44:23.415849+00:00
-- url     : https://prove2.me/theorems/36336628-20ef-4ccd-b03c-54d1bddd9cd6
-- title:
--   Cartwright Steger: index Cyclic Generator Matrix pow matrix Rank
-- statement:
--   The first cyclic-algebra relation at the actual selected place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSplitting.lean#L156-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSplitting.lean#L156-L164

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorMatrix_pow_matrixRank
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCyclicGeneratorMatrix P r level ^ r.matrixRank =
      (1 + indexPlaceY P r level) •
        (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) := by sorry
