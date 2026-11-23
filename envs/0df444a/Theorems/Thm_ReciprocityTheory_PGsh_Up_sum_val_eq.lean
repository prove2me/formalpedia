-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_sum_val_eq
-- name    : ReciprocityTheory.PGsh.Up.sum_val_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:09.280028+00:00
-- url     : https://prove2.me/theorems/15552911-8a8e-49c0-97e7-1ea529cf96d2
-- title:
--   Up: sum val eq
-- statement:
--   The Up construction uses the sum val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MatEquivApply.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MatEquivApply.lean#L23-L28

import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.PGsh.Up.sum_val_eq {n : ℕ} (j : ℕ) (f : Fin n → R) :
    ∑ k : Fin n, (if (k : ℕ) = j then f k else 0) = if h : j < n then f ⟨j, h⟩ else 0 := by sorry
