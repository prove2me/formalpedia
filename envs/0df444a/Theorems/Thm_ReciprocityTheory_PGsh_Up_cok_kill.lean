-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_cok_kill
-- name    : ReciprocityTheory.PGsh.Up.cok_kill
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:08:29.241866+00:00
-- url     : https://prove2.me/theorems/b58f8b8a-89d1-4c2c-89e9-a8b4afb2f433
-- title:
--   Up: cok kill
-- statement:
--   The Up construction uses the cok kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsFromRowsMulVecIff.lean#L109-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsFromRowsMulVecIff.lean#L109-L126

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

theorem ReciprocityTheory.PGsh.Up.cok_kill [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R} {E : Matrix (Ix g) (Ix g) R} {cp : R}
    (hcp : cp ≠ 0) (hE : IsUnit E.det) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) (hπi : π (π i) = i)
    (hHt : ∀ j, Ht * εT j = (εL (π j))ᵀ * Ht) :
    ∀ f ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ), ∃ t, Ht *ᵥ (εT (π i) *ᵥ t) = cp • f := by sorry
