-- Prove2me | Theorems.Thm_PretorsionImageClosed_Challenge_theoremA
-- name    : PretorsionImageClosed.Challenge.theoremA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T07:42:00.998444+00:00
-- url     : https://prove2.me/theorems/f354c6d7-aa39-5d6e-a823-4c71dedbc59e
-- title:
--   Challenge: theorem A
-- statement:
--   **Theorem A** (Theorem 4.4). For a subcategory `Z` of `mod Λ`, `Λ` a
--   finite-dimensional algebra over a field, the following are equivalent: `Z` is
--   image-closed; `Z = Gen Z ∩ Cogen Z`; `Z = T ∩ F` for a pretorsion theory
--   `(T, F)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/Solution.lean#L13-L14
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/Solution.lean#L13-L14

module
public import Definitions.Def_PretorsionImageClosed
public import Definitions.Def_PretorsionImageClosed_Solution
public import Theorems.Thm_PretorsionImageClosed_theoremA

set_option autoImplicit true
@[expose] public section
public section
universe u

theorem PretorsionImageClosed.Challenge.theoremA : PretorsionImageClosed.Statement.TheoremA.{u} := by sorry
