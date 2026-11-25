-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_fSum_succ
-- name    : PretorsionImageClosed.LinearQuiver.fSum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:22:24.286133+00:00
-- url     : https://prove2.me/theorems/9d915f08-89bf-5092-8b66-cbfd3c30af11
-- title:
--   Linear Quiver: f Sum succ
-- statement:
--   Equation (8.7): `Q_{n+1} = z Q_n + q z² Δ_q Q_n`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L426-L442
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L426-L442

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.fSum_succ (n : ℕ) :
    ∃ G, IsDelta (fSum n) G ∧ fSum (n + 1) = X * fSum n + C q * X ^ 2 * G := by sorry
