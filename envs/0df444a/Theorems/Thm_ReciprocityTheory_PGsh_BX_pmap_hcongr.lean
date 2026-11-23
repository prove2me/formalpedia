-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_pmap_hcongr
-- name    : ReciprocityTheory.PGsh.BX.pmap_hcongr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:56.948678+00:00
-- url     : https://prove2.me/theorems/f5a30dc5-392f-476b-b285-4a370861983c
-- title:
--   BX: pmap hcongr
-- statement:
--   The BX construction uses the pmap hcongr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L60-L63

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}

theorem ReciprocityTheory.PGsh.BX.pmap_hcongr {S : LAlg R₀} (f : LHom R S) {x₁ x₂ y₁ y₂ : B.G R} (hx : x₁ = x₂)
    (hy : y₁ = y₂) {u₁ : B.P R x₁ y₁} {u₂ : B.P R x₂ y₂} (hu : HEq u₁ u₂) :
    HEq (B.pmap f u₁) (B.pmap f u₂) := by sorry
