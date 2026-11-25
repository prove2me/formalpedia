-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_lastCount_succ
-- name    : PretorsionImageClosed.LinearQuiver.lastCount_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:04:20.451854+00:00
-- url     : https://prove2.me/theorems/2789d7a2-3ac4-453d-8e5e-c92686751c2b
-- title:
--   Linear Quiver: last Count succ
-- statement:
--   The Linear Quiver construction uses the last Count succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalFamilies.lean#L112-L131
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalFamilies.lean#L112-L131

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.lastCount_succ {m : ℕ} (D : IntervalFamily (m + 1)) :
    D.lastCount = (univ.filter (fun a : Fin (m + 1) => (a, Fin.last m) ∈ D.D)).card := by sorry
