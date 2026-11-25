-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_isPrecomplete_of_basis
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusGroupField.isPrecomplete_of_basis
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:07:37.49219+00:00
-- url     : https://prove2.me/theorems/3a7357c5-c611-495e-8ec5-b41cdb90f67b
-- title:
--   Frobenius Group Field: is Precomplete of basis
-- statement:
--   The Frobenius Group Field construction uses the is Precomplete of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsAdicCompleteOfBasis.lean#L31-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsAdicCompleteOfBasis.lean#L31-L55

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

theorem ReciprocityTheory.PGsh.Up.FrobeniusGroupField.isPrecomplete_of_basis {M : Type} [AddCommGroup M] [Module ℤ_[p] M] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ_[p] M) : IsPrecomplete (maximalIdeal ℤ_[p]) M := by sorry
