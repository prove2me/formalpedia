-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_key_step
-- name    : ReciprocityTheory.PGsh.Up.key_step
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:41.39669+00:00
-- url     : https://prove2.me/theorems/022d5562-91a2-4150-8b86-41e7140badb3
-- title:
--   Up: key step
-- statement:
--   The Up construction uses the key step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L56-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L56-L107

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

theorem ReciprocityTheory.PGsh.Up.key_step (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) :
    ∀ (N : ℕ) (α : ι → ZMod p), ∑ j, (α j).val = N → ∀ l,
      (fun x => lam Cm l x * monF Cm α x) ∈
        Submodule.span k (Set.range (monF (p := p) Cm)) := by sorry
