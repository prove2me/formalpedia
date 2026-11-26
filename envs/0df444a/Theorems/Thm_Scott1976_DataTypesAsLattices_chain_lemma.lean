-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_chain_lemma
-- name    : Scott1976.DataTypesAsLattices.chain_lemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:06.846114+00:00
-- url     : https://prove2.me/theorems/30ffef2d-6dbf-424a-b6ce-09d1dc817bd4
-- title:
--   Data Types As Lattices: chain lemma
-- statement:
--   **Scott 1976, Appendix lemma.** Continuous maps preserve ascending
--   countable unions.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L99-L124
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L99-L124

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.chain_lemma {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (xs : ℕ → Pomega) (hmono : ∀ n, xs n ⊆ xs (n + 1)) :
    f (⋃ n, xs n) = ⋃ n, f (xs n) := by sorry
