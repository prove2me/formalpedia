-- Prove2me | Theorems.Thm_TunnellMap_OrthogonalFrame_linComb3_injective
-- name    : TunnellMap.OrthogonalFrame.linComb3_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:56.396988+00:00
-- url     : https://prove2.me/theorems/5ae8613d-ab9e-533b-aa12-7157f3046468
-- title:
--   Orthogonal Frame: lin Comb3 injective
-- statement:
--   The Orthogonal Frame construction uses the lin Comb3 injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L134-L144
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L134-L144

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.OrthogonalFrame.linComb3_injective :
    Function.Injective (fun abc : ℤ × ℤ × ℤ =>
      linComb3 abc.1 abc.2.1 abc.2.2 F.e₁ F.e₂ F.z) := by sorry
