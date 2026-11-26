-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_6_2
-- name    : Scott1976.DataTypesAsLattices.theorem_6_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:31.833364+00:00
-- url     : https://prove2.me/theorems/a9656b74-5b3a-5458-b99d-8dc890ac29c4
-- title:
--   Data Types As Lattices: theorem 6 2
-- statement:
--   **Scott 1976, Theorem 6.2 (The 𝔉 theorem).** Complements of the sets
--   in Theorem 6.1 are the closed sets `{x | f(x) = ⊥}` when `f` takes only
--   `⊥` and `⊤`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L65-L79
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L65-L79

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Classification
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_6_2 {f : Pomega → Pomega} (_hf : IsScottContinuous f)
    (hval : ∀ x, f x = botElem ∨ f x = topElem) :
    {x | f x = botElem} = {x | 0 ∈ f x}ᶜ := by sorry
