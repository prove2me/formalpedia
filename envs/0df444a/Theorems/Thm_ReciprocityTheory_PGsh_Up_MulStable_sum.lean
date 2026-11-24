-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_sum
-- name    : ReciprocityTheory.PGsh.Up.MulStable.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:08.561079+00:00
-- url     : https://prove2.me/theorems/a094dded-e7ba-41e5-9bc4-2b35092b0f51
-- title:
--   Mul Stable: sum
-- statement:
--   The Mul Stable construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L143-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L143-L152

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

theorem ReciprocityTheory.PGsh.Up.MulStable.sum {S : Submodule k ((ι → ZMod p) → k)} {s : Finset ι}
    {h : ι → (ι → ZMod p) → k} (a : ∀ i ∈ s, MulStable S (h i)) :
    MulStable S (∑ i ∈ s, h i) := by sorry
