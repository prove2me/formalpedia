-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_prod_erase_update
-- name    : ReciprocityTheory.PGsh.Up.prod_erase_update
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:08:41.358721+00:00
-- url     : https://prove2.me/theorems/d0b18a60-febd-4f1c-8654-7f8bbf3bac97
-- title:
--   Up: prod erase update
-- statement:
--   The Up construction uses the prod erase update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L44-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] {ι : Type} [Fintype ι]
  [DecidableEq ι]

theorem ReciprocityTheory.PGsh.Up.prod_erase_update (Cm : Matrix ι ι k) (α : ι → ZMod p) (l : ι) (a : ZMod p)
    (x : ι → ZMod p) :
    ∏ j ∈ univ.erase l, lam Cm j x ^ (Function.update α l a j).val =
      ∏ j ∈ univ.erase l, lam Cm j x ^ (α j).val := by sorry
