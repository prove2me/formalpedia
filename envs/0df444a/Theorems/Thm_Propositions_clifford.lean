-- Prove2me | Theorems.Thm_Propositions_clifford
-- name    : Propositions.clifford
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:54:30.328264+00:00
-- url     : https://prove2.me/theorems/07987044-d4cb-42b1-be73-791cf8e6d9f2
-- title:
--   Propositions: clifford
-- statement:
--   The Propositions construction uses the clifford property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/PalomarSolution.lean#L26-L36
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/PalomarSolution.lean#L26-L36

module
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
public import Definitions.Def_ChipFiringWithLean_PalomarSolution
set_option autoImplicit true
@[expose] public section
public section
open Propositions

theorem Propositions.clifford {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
    ∀ r rdual : ℤ, rank_eq G D r → rank_eq G (canonical_divisor G - D) rdual →
      0 ≤ r → 0 ≤ rdual → (r : ℚ) ≤ (deg D : ℚ) / 2 := by sorry
