-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_monF_split
-- name    : ReciprocityTheory.PGsh.Up.monF_split
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:47.738926+00:00
-- url     : https://prove2.me/theorems/ed87ad5d-73b0-4e63-acb5-55d5b5811381
-- title:
--   Up: mon F split
-- statement:
--   The Up construction uses the mon F split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L39-L42

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

theorem ReciprocityTheory.PGsh.Up.monF_split (Cm : Matrix ι ι k) (α : ι → ZMod p) (l : ι) (x : ι → ZMod p) :
    monF Cm α x = lam Cm l x ^ (α l).val * ∏ j ∈ univ.erase l, lam Cm j x ^ (α j).val := by sorry
