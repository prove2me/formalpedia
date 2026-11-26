-- Prove2me | Theorems.Thm_TunnellMap_OrthogonalFrame_affine_norm_expansion
-- name    : TunnellMap.OrthogonalFrame.affine_norm_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:47:26.197445+00:00
-- url     : https://prove2.me/theorems/b7434e68-d037-4904-95ee-aedf4423b284
-- title:
--   Orthogonal Frame: affine norm expansion
-- statement:
--   The Orthogonal Frame construction uses the affine norm expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L171-L179
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L171-L179

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.OrthogonalFrame.affine_norm_expansion (t a b : ℤ) :
    dot (linComb3 a b t F.e₁ F.e₂ F.z)
      (linComb3 a b t F.e₁ F.e₂ F.z) =
      dot F.e₁ F.e₁ * a ^ 2 +
      2 * (dot F.e₁ F.e₂ * b + t * dot F.z F.e₁) * a +
      dot F.e₂ F.e₂ * b ^ 2 +
      2 * t * dot F.z F.e₂ * b + t ^ 2 * dot F.z F.z := by sorry
