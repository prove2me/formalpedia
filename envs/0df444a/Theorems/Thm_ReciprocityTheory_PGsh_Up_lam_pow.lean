-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_lam_pow
-- name    : ReciprocityTheory.PGsh.Up.lam_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:05.836438+00:00
-- url     : https://prove2.me/theorems/d623fd4a-f031-593b-827e-7e946d0c2967
-- title:
--   Up: lam pow
-- statement:
--   The Up construction uses the lam pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L23-L25

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

theorem ReciprocityTheory.PGsh.Up.lam_pow (Cm : Matrix ι ι k) (j : ι) (x : ι → ZMod p) :
    lam Cm j x ^ p = ∑ i, Cm j i ^ p * xc k i x := by sorry
