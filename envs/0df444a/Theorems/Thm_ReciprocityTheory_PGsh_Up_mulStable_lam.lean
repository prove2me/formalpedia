-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_mulStable_lam
-- name    : ReciprocityTheory.PGsh.Up.mulStable_lam
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:47.923841+00:00
-- url     : https://prove2.me/theorems/2ebc79e3-d5a0-5dd4-901e-f456d95c1442
-- title:
--   Up: mul Stable lam
-- statement:
--   The Up construction uses the mul Stable lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L113-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L113-L122

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

theorem ReciprocityTheory.PGsh.Up.mulStable_lam (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) (l : ι) :
    MulStable (Submodule.span k (Set.range (monF (p := p) Cm))) (lam Cm l) := by sorry
