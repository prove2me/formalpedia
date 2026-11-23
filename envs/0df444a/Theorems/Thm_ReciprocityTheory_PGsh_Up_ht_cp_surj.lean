-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_ht_cp_surj
-- name    : ReciprocityTheory.PGsh.Up.ht_cp_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:12.93923+00:00
-- url     : https://prove2.me/theorems/1f499681-be44-44bd-868d-304f112a494d
-- title:
--   Up: ht cp surj
-- statement:
--   The Up construction uses the ht cp surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLowerBoundOf.lean#L64-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLowerBoundOf.lean#L64-L83

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
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

theorem ReciprocityTheory.PGsh.Up.ht_cp_surj {R : Type} [CommRing R] [IsDomain R] {g : ℕ} (Ht Bt : Matrix (Fin g) (Ix g) R)
    (E : Matrix (Ix g) (Ix g) R) (cp : R) (hEt : Eᵀ = -E) (hdiag : ∀ i, E i i = 0)
    (hdet : IsUnit E.det) (hc : cp ≠ 0) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E) :
    ∀ f : Fin g → R, ∃ t, Ht *ᵥ t = cp • f := by sorry
