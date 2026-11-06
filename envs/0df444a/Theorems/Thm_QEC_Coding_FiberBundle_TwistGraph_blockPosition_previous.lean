-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockPosition_previous
-- name    : QEC.Coding.FiberBundle.TwistGraph.blockPosition_previous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:45:40.738566+00:00
-- url     : https://prove2.me/theorems/1651b00d-6037-4ce4-88b1-caefdad4bcc3
-- title:
--   Twist Graph: block Position previous
-- statement:
--   The last position of the preceding block is the preceding fine cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L175-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L175-L205

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.blockPosition_previous
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (u : ZMod ell) :
    blockPosition ell
        (u - 1, ⟨ell - 1,
          Nat.sub_lt (NeZero.pos ell) Nat.zero_lt_one⟩) =
      layerEmbedding ell u - 1 := by sorry
