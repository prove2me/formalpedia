-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul_tensor_eq_zero
-- name    : ReciprocityTheory.PGsh.BX.nsmul_tensor_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:08.542992+00:00
-- url     : https://prove2.me/theorems/4c2625e4-5c71-50a9-b14e-577b8af25de0
-- title:
--   BX: nsmul tensor eq zero
-- statement:
--   The BX construction uses the nsmul tensor eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulTensorEqZero.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulTensorEqZero.lean#L23-L33

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

theorem ReciprocityTheory.PGsh.BX.nsmul_tensor_eq_zero {A : Type u} [CommRing A] [Algebra R₀ A] {N : ℕ}
    (hN : (N : A) = 0) (K : Submodule R₀ A) (Y : B.gg ⊗[R₀] K) : N • Y = 0 := by sorry
