-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_FP_isFibreSq
-- name    : ReciprocityTheory.PGsh.FP.isFibreSq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:18.240236+00:00
-- url     : https://prove2.me/theorems/e804a7f2-4250-50a6-8b88-96bc7847f9ad
-- title:
--   FP: is Fibre Sq
-- statement:
--   The FP construction uses the is Fibre Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L116-L120

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
variable {R₁ R₂ R : LAlg R₀} (f₁ : LHom R₁ R) (f₂ : LHom R₂ R)

theorem ReciprocityTheory.PGsh.FP.isFibreSq (h₁ : f₁.NilSurj) (h₂ : f₂.NilSurj) :
    IsFibreSq (FP.p₁ f₁ f₂) (FP.p₂ f₁ f₂) f₁ f₂ := by sorry
