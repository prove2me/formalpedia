-- Prove2me | Theorems.Thm_TunnellMap_Examples41_lattice_frame_example
-- name    : TunnellMap.Examples41.lattice_frame_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:07:49.950677+00:00
-- url     : https://prove2.me/theorems/b89ebd78-d896-4cde-adae-955077664abc
-- title:
--   Examples41: lattice frame example
-- statement:
--   The Examples41 construction uses the lattice frame example property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L27-L34
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L27-L34

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.lattice_frame_example :
    tau (residualSourceLift s2) = ⟨0, -5, -4⟩ ∧
      frame41.e₁ = ⟨1, 0, 0⟩ ∧
      frame41.e₂ = ⟨0, -4, 5⟩ ∧
      frame41.z = ⟨0, -1, 1⟩ ∧
      cross frame41.e₁ frame41.e₂ = tau (residualSourceLift s2) ∧
      dot (tau (residualSourceLift s2)) frame41.z = 1 := by sorry
