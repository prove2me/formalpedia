-- Prove2me | Theorems.Thm_TunnellMap_OrthogonalFrame_affine_norm_eq_iff
-- name    : TunnellMap.OrthogonalFrame.affine_norm_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:26.646146+00:00
-- url     : https://prove2.me/theorems/8c47f7ba-8834-4772-94ca-7c86fba2627b
-- title:
--   Orthogonal Frame: affine norm eq iff
-- statement:
--   Equation (5.4): the affine vector has norm `A` exactly when its first
--   coordinate satisfies the displayed quadratic.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuadraticRoots.lean#L81-L87
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuadraticRoots.lean#L81-L87

import Definitions.Def_TunnellMap_ShortInterval
import Definitions.Def_TunnellMap_QuadraticRoots
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.OrthogonalFrame.affine_norm_eq_iff (A q a b : ℤ) :
    dot (linComb3 a b (q * A) F.e₁ F.e₂ F.z)
        (linComb3 a b (q * A) F.e₁ F.e₂ F.z) = A ↔
      F.affineQuadratic A q a b = 0 := by sorry
