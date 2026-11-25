-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul_of_same_red
-- name    : ReciprocityTheory.PGsh.BX.nsmul_of_same_red
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:05:44.856186+00:00
-- url     : https://prove2.me/theorems/0bb9caa0-39b1-4d90-a865-3619e02237fa
-- title:
--   BX: nsmul of same red
-- statement:
--   The BX construction uses the nsmul of same red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulTensorEqZero.lean#L35-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulTensorEqZero.lean#L35-L74

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

theorem ReciprocityTheory.PGsh.BX.nsmul_of_same_red {N : ℕ} (hN : (N : (R : Type u)) = 0) {x y : B.G Dp.D}
    {x₀ y₀ : B.G R} (e : B.P R x₀ y₀) (u v : B.P Dp.D x y) (hu : HEq (B.pmap Dp.π u) e)
    (hv : HEq (B.pmap Dp.π v) e) : B.nsmul1 u N = B.nsmul1 v N ∧ B.nsmul2 u N = B.nsmul2 v N := by sorry
