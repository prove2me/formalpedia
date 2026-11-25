-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_ht_ext
-- name    : ReciprocityTheory.PGsh.ht_ext
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:20.802172+00:00
-- url     : https://prove2.me/theorems/9ac1b1d5-be59-4511-a285-f5c7eae58691
-- title:
--   PGsh: ht ext
-- statement:
--   The PGsh construction uses the ht ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L177-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L177-L216

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

theorem ReciprocityTheory.PGsh.ht_ext (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (hy : N • y = 0) (hH : B.IsHeight Dp N y h)
    (V : B.gg ⊗[R₀] (R : Type u)) :
    ∃ z : (Dp.D : Type u)ˣ,
      B.IsPairing N (B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap V)) (B.map Dp.σ y) z ∧
        (z : (Dp.D : Type u)) = 1 + Dp.σ.1 (hext B h V) * Dp.η := by sorry
