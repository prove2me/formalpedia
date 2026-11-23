-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_involutionPerm_apply
-- name    : ReciprocityTheory.PGsh.Up.involutionPerm_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:46:50.016428+00:00
-- url     : https://prove2.me/theorems/48f7330f-104f-4d97-b7c7-81e96f535ef2
-- title:
--   Up: involution Perm apply
-- statement:
--   The Up construction uses the involution Perm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InvolutionPermApplyZero.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InvolutionPermApplyZero.lean#L69-L72

import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelLengthComparisonOf
import Definitions.Def_ReciprocityTheory_DualLattices_StdJForm
import Definitions.Def_ReciprocityTheory_DualLattices_InvolutionPermApplyZero
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
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O}

theorem ReciprocityTheory.PGsh.Up.involutionPerm_apply {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i))
    (k : Fin m) (hk : e k ≠ 0) : pi2 e π hσ k = π k := by sorry
