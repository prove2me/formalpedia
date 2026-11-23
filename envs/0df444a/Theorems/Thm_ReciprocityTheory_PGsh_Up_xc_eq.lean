-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_xc_eq
-- name    : ReciprocityTheory.PGsh.Up.xc_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:30.220817+00:00
-- url     : https://prove2.me/theorems/e36b6d45-60fb-49e0-9b77-3fc446bd0959
-- title:
--   Up: xc eq
-- statement:
--   The Up construction uses the xc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L27-L34

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

theorem ReciprocityTheory.PGsh.Up.xc_eq (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) (i : ι) (x : ι → ZMod p) :
    xc k i x = ∑ m, Cinv i m * lam Cm m x := by sorry
