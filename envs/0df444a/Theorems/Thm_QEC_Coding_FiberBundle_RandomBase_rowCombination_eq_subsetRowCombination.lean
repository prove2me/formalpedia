-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_rowCombination_eq_subsetRowCombination
-- name    : QEC.Coding.FiberBundle.RandomBase.rowCombination_eq_subsetRowCombination
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:29:06.543444+00:00
-- url     : https://prove2.me/theorems/962d9952-a790-48a3-9fc9-95d553df5f1a
-- title:
--   Random Base: row Combination eq subset Row Combination
-- statement:
--   A binary coefficient vector is exactly the indicator of its support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L253-L266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L253-L266

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u

theorem QEC.Coding.FiberBundle.RandomBase.rowCombination_eq_subsetRowCombination
    {r : Nat} (sample : Sample r)
    (coeff : Fin (3 * r) → ZMod 2) :
    rowCombination sample coeff =
      subsetRowCombination sample (rowSupport coeff) := by sorry
