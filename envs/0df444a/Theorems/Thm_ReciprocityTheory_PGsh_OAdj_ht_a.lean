-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_OAdj_ht_a
-- name    : ReciprocityTheory.PGsh.OAdj.ht_a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:06:19.090964+00:00
-- url     : https://prove2.me/theorems/a0b46fb9-a99f-4aac-9390-f8e2a24fa0da
-- title:
--   OAdj: ht a
-- statement:
--   The OAdj construction uses the ht a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L222-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L222-L236

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
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
open ReciprocityTheory.PGsh.OAdj
variable {B : BX R₀} {O : LAlg R₀} (A : OAdj B O) {R : LAlg R₀} (s : LHom O R)

theorem ReciprocityTheory.PGsh.OAdj.ht_a (Dp : DualPair R) (N : ℕ) (y : B.G R) (h : B.gg →ₗ[R₀] (R : Type u))
    (δ : B.gg →ₗ[R₀] B.gg ⊗[R₀] (R : Type u)) (hy : N • y = 0) (hH : B.IsHeight Dp N y h)
    (hδ : ∀ v, A.ab.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap (δ v))) :
    B.IsHeight Dp N (A.a.f s y) (hext B h ∘ₗ δ) := by sorry
