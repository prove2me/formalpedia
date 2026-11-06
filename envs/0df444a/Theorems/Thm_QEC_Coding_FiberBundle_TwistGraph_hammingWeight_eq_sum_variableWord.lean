-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hammingWeight_eq_sum_variableWord
-- name    : QEC.Coding.FiberBundle.TwistGraph.hammingWeight_eq_sum_variableWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:46:42.912785+00:00
-- url     : https://prove2.me/theorems/e07de155-e270-4f21-9858-f76f9a356d6c
-- title:
--   Twist Graph: hamming Weight eq sum variable Word
-- statement:
--   Total twist-word weight is also the sum over base-variable columns.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L506-L518
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L506-L518

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.hammingWeight_eq_sum_variableWord
    {r ell : Nat}
    [NeZero ell]
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    HammingWeight w =
      ∑ b : Fin (4 * r), HammingWeight (variableWord w b) := by sorry
