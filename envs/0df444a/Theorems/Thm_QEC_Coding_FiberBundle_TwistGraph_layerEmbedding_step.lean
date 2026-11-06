-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_layerEmbedding_step
-- name    : QEC.Coding.FiberBundle.TwistGraph.layerEmbedding_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:42:29.054816+00:00
-- url     : https://prove2.me/theorems/90c9ccdf-f68b-4a8e-8bed-ef99f0a39639
-- title:
--   Twist Graph: layer Embedding step
-- statement:
--   A reduced graph step embeds as the corresponding full bundle rotation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L241-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L241-L252

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.layerEmbedding_step
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) :
    layerEmbedding ell (step sample τ) =
      multipleRotation ell
        ⟨(RandomTwist.typeTwist sample τ).val + 1, by
          have h := (RandomTwist.typeTwist sample τ).isLt
          omega⟩ := by sorry
