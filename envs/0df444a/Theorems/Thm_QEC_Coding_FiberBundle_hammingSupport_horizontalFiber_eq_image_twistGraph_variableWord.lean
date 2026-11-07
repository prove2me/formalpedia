-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingSupport_horizontalFiber_eq_image_twistGraph_variableWord
-- name    : QEC.Coding.FiberBundle.hammingSupport_horizontalFiber_eq_image_twistGraph_variableWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:09.909884+00:00
-- url     : https://prove2.me/theorems/65f0f57f-914c-4518-8612-df7b6be5b7ba
-- title:
--   Fiber Bundle: hamming Support horizontal Fiber eq image twist Graph variable Word
-- statement:
--   For a residue-normalized representative, a horizontal fiber is supported
--   exactly on the image of its twist-graph column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2083-L2126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2083-L2126

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingSupport_horizontalFiber_eq_image_twistGraph_variableWord
    {r ell : Nat}
    [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hNormalized : IsHorizontallyResidueNormalized z)
    (b : Fin (4 * r)) :
    hammingSupport (horizontalFiber z b) =
      (hammingSupport
        (TwistGraph.variableWord
          (twistGraphWordOfHorizontalComponent z) b)).image
        (TwistGraph.layerEmbedding ell) := by sorry
