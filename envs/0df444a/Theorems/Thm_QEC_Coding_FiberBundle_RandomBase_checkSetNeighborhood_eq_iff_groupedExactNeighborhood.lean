-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_checkSetNeighborhood_eq_iff_groupedExactNeighborhood
-- name    : QEC.Coding.FiberBundle.RandomBase.checkSetNeighborhood_eq_iff_groupedExactNeighborhood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:52:54.198951+00:00
-- url     : https://prove2.me/theorems/9be830e2-ad98-4729-9932-682a0e16d15e
-- title:
--   Random Base: check Set Neighborhood eq iff grouped Exact Neighborhood
-- statement:
--   Regrouping identifies exact-neighborhood and per-column hit/avoid events.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L529-L586
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L529-L586

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.checkSetNeighborhood_eq_iff_groupedExactNeighborhood
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    checkSetNeighborhood sample S = T ↔
      GroupedExactNeighborhood S T (sampleEquivGrouped r sample) := by sorry
