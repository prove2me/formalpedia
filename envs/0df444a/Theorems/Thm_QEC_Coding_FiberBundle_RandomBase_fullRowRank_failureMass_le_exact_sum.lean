-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_fullRowRank_failureMass_le_exact_sum
-- name    : QEC.Coding.FiberBundle.RandomBase.fullRowRank_failureMass_le_exact_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:30:34.292581+00:00
-- url     : https://prove2.me/theorems/7c23a346-2c3e-4285-aafb-f7bed91269a6
-- title:
--   Random Base: full Row Rank failure Mass le exact sum
-- statement:
--   Union bound for full-row-rank failure, with the exact fixed-subset probability
--   still visible for the paper's subsequent small- and large-weight split.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L746-L771
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L746-L771

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

theorem QEC.Coding.FiberBundle.RandomBase.fullRowRank_failureMass_le_exact_sum
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (@HasFullRowRank r) ≤
      ∑ A : {A : Finset (Fin (3 * r)) // A.Nonempty},
        (ENNReal.ofReal
          ((1 +
            (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^
              A.1.card) / 2)) ^ (4 * r) := by sorry
