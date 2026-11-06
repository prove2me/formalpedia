-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_layerEmbedding_injective
-- name    : QEC.Coding.FiberBundle.TwistGraph.layerEmbedding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:45:35.681082+00:00
-- url     : https://prove2.me/theorems/be6db6c9-c961-41c1-9506-36f6913a527a
-- title:
--   Twist Graph: layer Embedding injective
-- statement:
--   Distinct twist-graph layers embed at distinct residue-zero fiber cells.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L68-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L68-L111

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.layerEmbedding_injective
    (ell : Nat) [NeZero ell] :
    Function.Injective (layerEmbedding ell) := by sorry
