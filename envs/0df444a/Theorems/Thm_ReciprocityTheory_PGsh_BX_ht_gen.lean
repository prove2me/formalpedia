-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_ht_gen
-- name    : ReciprocityTheory.PGsh.BX.ht_gen
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:00.86324+00:00
-- url     : https://prove2.me/theorems/112c1b5b-cf65-453e-8491-64f3ff7d2c13
-- title:
--   BX: ht gen
-- statement:
--   The BX construction uses the ht gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulTensorEqZero.lean#L100-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulTensorEqZero.lean#L100-L268

import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
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
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R)

theorem ReciprocityTheory.PGsh.BX.ht_gen (hB2 : HighestWeightVectorUniformBounds B) (N : ℕ) (hN : (N : (R : Type u)) = 0) (y : B.G R)
    (h : B.gg →ₗ[R₀] R) (hh : B.IsHeight Dp N y h) (Y : B.gg ⊗[R₀] Dp.π.ker)
    (w₀ : B.P Dp.D (B.tg Dp.π Dp.sqZero Y) (B.map Dp.σ y))
    (hu : HEq (B.pmap Dp.π w₀) (B.zero1 y)) :
    HEq (B.nsmul1 w₀ N) (B.zero1 (B.map Dp.σ y)) ∧
    ∃ c : (Dp.D : Type u)ˣ,
      (c : (Dp.D : Type u)) = 1 - evalT (Dp.σ.1.toLinearMap ∘ₗ h) Dp.π.ker Y ∧
      HEq (B.nsmul2 w₀ N) (B.smul c (B.zero2 (B.tg Dp.π Dp.sqZero Y))) := by sorry
