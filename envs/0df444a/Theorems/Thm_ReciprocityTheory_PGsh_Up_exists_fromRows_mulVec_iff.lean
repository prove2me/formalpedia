-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_exists_fromRows_mulVec_iff
-- name    : ReciprocityTheory.PGsh.Up.exists_fromRows_mulVec_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:06:38.496594+00:00
-- url     : https://prove2.me/theorems/0e35ba86-d1c9-4637-a334-319a1fb4dd43
-- title:
--   Up: exists from Rows mul Vec iff
-- statement:
--   The Up construction uses the exists from Rows mul Vec iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsFromRowsMulVecIff.lean#L70-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsFromRowsMulVecIff.lean#L70-L107

import Definitions.Def_ReciprocityTheory_DualLattices_LenIdBStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFromRowsMulVecIff
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
variable {R : Type} [CommRing R] {g : ℕ}
variable {m : ℕ}

theorem ReciprocityTheory.PGsh.Up.exists_fromRows_mulVec_iff [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R} {E : Matrix (Ix g) (Ix g) R} {cp : R}
    (hcp : cp ≠ 0) (hE : IsUnit E.det) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) (hHt : Ht * εT i = (εL (π i))ᵀ * Ht)
    (hBt : Bt * εT i = εL i * Bt) (x : Fin g → R) (hx : εL i *ᵥ x = x) :
    (∃ t, fromRows Ht Bt *ᵥ (εT i *ᵥ t) = Sum.elim (0 : Fin g → R) x) ↔
      ∃ z, Htᵀ *ᵥ x = cp • z := by sorry
