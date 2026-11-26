-- Prove2me | Theorems.Thm_TunnellMap_OrthogonalFrame_affine_coset
-- name    : TunnellMap.OrthogonalFrame.affine_coset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:44.721536+00:00
-- url     : https://prove2.me/theorems/8491e3b8-30ae-5224-8193-23fd1d919c37
-- title:
--   Orthogonal Frame: affine coset
-- statement:
--   Lemma 5.2: integral solutions of `p·r=t` are uniquely parametrized by
--   `r=t z+a e₁+b e₂`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L148-L169
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L148-L169

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.OrthogonalFrame.affine_coset (t : ℤ) (r : Triple) (hr : dot p r = t) :
    ∃! ab : ℤ × ℤ,
      r = linComb3 ab.1 ab.2 t F.e₁ F.e₂ F.z := by sorry
