-- Prove2me | Theorems.Thm_TunnellMap_reduceFrame_deterministic
-- name    : TunnellMap.reduceFrame_deterministic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:53:19.454936+00:00
-- url     : https://prove2.me/theorems/75c4f6e5-46a5-51a5-acc8-b2f291058dce
-- title:
--   Tunnell Map: reduce Frame deterministic
-- statement:
--   **Determinism of the reduced frame.**  The reduced basis depends only on
--   the input basis vectors — not on the Bezout vector, the ambient source vector,
--   or the proofs carried by the frame.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L352-L356
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L352-L356

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}

theorem TunnellMap.reduceFrame_deterministic {p q : Triple} (F : OrthogonalFrame p)
    (G : OrthogonalFrame q) (h₁ : F.e₁ = G.e₁) (h₂ : F.e₂ = G.e₂) :
    ((reduceFrame F).e₁, (reduceFrame F).e₂) =
      ((reduceFrame G).e₁, (reduceFrame G).e₂) := by sorry
