-- Prove2me | Theorems.Thm_PretorsionImageClosed_theoremA
-- name    : PretorsionImageClosed.theoremA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:48:20.798465+00:00
-- url     : https://prove2.me/theorems/0798136d-7de5-46a1-b5ca-437587b6f185
-- title:
--   Pretorsion Image Closed: theorem A
-- statement:
--   **Theorem A** (Theorem 4.4).
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/MainTheorems.lean#L44-L49
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/MainTheorems.lean#L44-L49

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Definitions.Def_PretorsionImageClosed_MainTheorems
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
universe u

theorem PretorsionImageClosed.theoremA : Statement.TheoremA.{u} := by sorry
