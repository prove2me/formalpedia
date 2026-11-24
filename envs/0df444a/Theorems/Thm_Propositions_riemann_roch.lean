-- Prove2me | Theorems.Thm_Propositions_riemann_roch
-- name    : Propositions.riemann_roch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:54:27.375574+00:00
-- url     : https://prove2.me/theorems/c961366c-1550-4870-b719-f3dbb578e26c
-- title:
--   Propositions: riemann roch
-- statement:
--   The Propositions construction uses the riemann roch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/PalomarSolution.lean#L15-L24
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/PalomarSolution.lean#L15-L24

module
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
public import Definitions.Def_ChipFiringWithLean_PalomarSolution
set_option autoImplicit true
@[expose] public section
public section
open Propositions

theorem Propositions.riemann_roch {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
    ∀ r rdual : ℤ, rank_eq G D r → rank_eq G (canonical_divisor G - D) rdual →
      r - rdual = deg D + 1 - genus G := by sorry
