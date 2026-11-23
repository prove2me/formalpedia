-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_hcongr
-- name    : ReciprocityTheory.PGsh.BX.nsmul1_hcongr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:44.439798+00:00
-- url     : https://prove2.me/theorems/12aec997-83b5-4e00-85e7-d81e01011cc7
-- title:
--   BX: nsmul1 hcongr
-- statement:
--   The BX construction uses the nsmul1 hcongr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L65-L68

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

theorem ReciprocityTheory.PGsh.BX.nsmul1_hcongr {x₁ x₂ y₁ y₂ : B.G R} (hx : x₁ = x₂) (hy : y₁ = y₂) (n : ℕ)
    {u₁ : B.P R x₁ y₁} {u₂ : B.P R x₂ y₂} (hu : HEq u₁ u₂) :
    HEq (B.nsmul1 u₁ n) (B.nsmul1 u₂ n) := by sorry
