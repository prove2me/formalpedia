-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_cpSum_eq
-- name    : PretorsionImageClosed.LinearQuiver.cpSum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:47:48.286931+00:00
-- url     : https://prove2.me/theorems/d54a8a88-afa8-4ad5-95c2-6d9058129c93
-- title:
--   Linear Quiver: cp Sum eq
-- statement:
--   Theorem 7.5 in cutoff coordinates: `cpSum n = B_{n+1}`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L540-L547
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L540-L547

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.cpSum_eq {B : ℕ → Rq[X]} (hB : IsGandhiFirst B) (n : ℕ) : cpSum n = B (n + 1) := by sorry
