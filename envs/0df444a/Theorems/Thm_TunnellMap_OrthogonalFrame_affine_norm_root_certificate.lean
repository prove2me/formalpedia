-- Prove2me | Theorems.Thm_TunnellMap_OrthogonalFrame_affine_norm_root_certificate
-- name    : TunnellMap.OrthogonalFrame.affine_norm_root_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:48.64479+00:00
-- url     : https://prove2.me/theorems/5f9d1d65-fbb5-4769-a611-72dc0f56f461
-- title:
--   Orthogonal Frame: affine norm root certificate
-- statement:
--   The exact integral-root interface used by Algorithm 5.4.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuadraticRoots.lean#L103-L134
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuadraticRoots.lean#L103-L134

import Definitions.Def_TunnellMap_ShortInterval
import Definitions.Def_TunnellMap_QuadraticRoots
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.OrthogonalFrame.affine_norm_root_certificate (A q a b : ℤ) :
    dot (linComb3 a b (q * A) F.e₁ F.e₂ F.z)
        (linComb3 a b (q * A) F.e₁ F.e₂ F.z) = A ↔
      ∃ u : ℤ,
        u ^ 2 = F.halfDiscriminant A q b ∧
        dot F.e₁ F.e₁ * a =
          -(dot F.e₁ F.e₂ * b + q * A * dot F.z F.e₁) + u := by sorry
