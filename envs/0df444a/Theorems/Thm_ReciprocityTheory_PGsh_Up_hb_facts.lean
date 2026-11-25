-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_hb_facts
-- name    : ReciprocityTheory.PGsh.Up.hb_facts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:33.972801+00:00
-- url     : https://prove2.me/theorems/db996060-1971-4282-94d5-a606dc22ac45
-- title:
--   Up: hb facts
-- statement:
--   The Up construction uses the hb facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsFromRowsMulVecIff.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsFromRowsMulVecIff.lean#L58-L66

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

theorem ReciprocityTheory.PGsh.Up.hb_facts [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R} {E : Matrix (Ix g) (Ix g) R} {cp : R}
    (hcp : cp ≠ 0) (hE : IsUnit E.det) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E) :
    Ht * ((Eᵀ)⁻¹ * Htᵀ) = 0 ∧ Bt * ((Eᵀ)⁻¹ * Htᵀ) = cp • (1 : Matrix (Fin g) (Fin g) R) := by sorry
