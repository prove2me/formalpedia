-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_xc_pow
-- name    : ReciprocityTheory.PGsh.Up.xc_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:05.719395+00:00
-- url     : https://prove2.me/theorems/bf769621-2b41-5492-8bc9-16f24d21fb2c
-- title:
--   Up: xc pow
-- statement:
--   The Up construction uses the xc pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L20-L21

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

theorem ReciprocityTheory.PGsh.Up.xc_pow (i : ι) (x : ι → ZMod p) : xc k i x ^ p = xc k i x := by sorry
