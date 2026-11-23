-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_involutionPerm_involutive
-- name    : ReciprocityTheory.PGsh.Up.involutionPerm_involutive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:32.999458+00:00
-- url     : https://prove2.me/theorems/4a2f4f20-fcb6-4eba-97cc-0c722d1c23a6
-- title:
--   Up: involution Perm involutive
-- statement:
--   The Up construction uses the involution Perm involutive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InvolutionPermApplyZero.lean#L86-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InvolutionPermApplyZero.lean#L86-L103

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

theorem ReciprocityTheory.PGsh.Up.involutionPerm_involutive {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i))
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hinv : ∀ a, σ (σ a) = a) (k : Fin m) :
    pi2 e π hσ (pi2 e π hσ k) = k := by sorry
