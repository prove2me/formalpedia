-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_layer_cardinality_bounds_of_small
-- name    : QEC.Coding.FiberBundle.TwistGraph.layer_cardinality_bounds_of_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:46.721234+00:00
-- url     : https://prove2.me/theorems/88bf1ccd-9693-4b27-b134-1bb4b8f83ef9
-- title:
--   Twist Graph: layer cardinality bounds of small
-- statement:
--   The small global word bound forces the cardinality estimates used before the
--   two cases of HHO20 `thm:ltc`:
--
--   * `|H| / ell ≤ .00005`;
--   * `|L| / ell ≥ .9999`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L67-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L67-L168

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.layer_cardinality_bounds_of_small
    {r ell : Nat}
    [NeZero r] [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hsmall :
      5000 * Delta * HammingWeight w ≤ ell * (4 * r)) :
    20000 * (heavyLayerSet Delta w).card ≤ ell ∧
      9999 * ell ≤ 10000 * (lightLayerSet Delta w).card := by sorry
