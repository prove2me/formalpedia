-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_det_monF_ne_zero
-- name    : ReciprocityTheory.PGsh.Up.det_monF_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:31.320316+00:00
-- url     : https://prove2.me/theorems/393031e0-0902-43cf-8688-65d15087ca6b
-- title:
--   Up: det mon F ne zero
-- statement:
--   The Up construction uses the det mon F ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L223-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L223-L236

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

theorem ReciprocityTheory.PGsh.Up.det_monF_ne_zero (Cm : Matrix ι ι k) (hC : IsUnit Cm.det) :
    (Matrix.of fun (x α : ι → ZMod p) => monF Cm α x).det ≠ 0 := by sorry
