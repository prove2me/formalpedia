-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_smul_top_self
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusGroupField.smul_top_self
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:07:24.223483+00:00
-- url     : https://prove2.me/theorems/c7eb75d9-709b-4668-b201-7b0c84fdac8e
-- title:
--   Frobenius Group Field: smul top self
-- statement:
--   The Frobenius Group Field construction uses the smul top self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsAdicCompleteOfBasis.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsAdicCompleteOfBasis.lean#L11-L13

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {p : ℕ} [hp : Fact p.Prime]

theorem ReciprocityTheory.PGsh.Up.FrobeniusGroupField.smul_top_self (k : ℕ) :
    ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] ℤ_[p]) = (maximalIdeal ℤ_[p]) ^ k := by sorry
