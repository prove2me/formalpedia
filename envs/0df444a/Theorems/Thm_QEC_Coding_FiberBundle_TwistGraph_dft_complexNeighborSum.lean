-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_dft_complexNeighborSum
-- name    : QEC.Coding.FiberBundle.TwistGraph.dft_complexNeighborSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:52:14.584207+00:00
-- url     : https://prove2.me/theorems/73ac8ec6-eb7e-4936-99aa-24beeb69f4ef
-- title:
--   Twist Graph: dft complex Neighbor Sum
-- statement:
--   The cyclic twist-graph adjacency action is diagonal in the DFT basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L119-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L119-L137

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod

theorem QEC.Coding.FiberBundle.TwistGraph.dft_complexNeighborSum
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (g : ZMod ell → Complex)
    (frequency : ZMod ell) :
    ZMod.dft (complexNeighborSum twistSample g) frequency =
      cayleyMultiplier twistSample frequency *
        ZMod.dft g frequency := by sorry
