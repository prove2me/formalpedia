-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_coordK_lTensor
-- name    : ReciprocityTheory.PGsh.BX.coordK_lTensor
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:07:13.165094+00:00
-- url     : https://prove2.me/theorems/0579caa2-61b0-4a88-a588-2a9c14d92433
-- title:
--   BX: coord K l Tensor
-- statement:
--   The BX construction uses the coord K l Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsLimTensor.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsLimTensor.lean#L68-L74

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulKerZero
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsLimTensor
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
variable (B : BX R₀) {p : ℕ}

theorem ReciprocityTheory.PGsh.BX.coordK_lTensor {M M' : Type u} [AddCommGroup M] [Module R₀ M] [AddCommGroup M'] [Module R₀ M']
    (f : M →ₗ[R₀] M') (k : Module.Free.ChooseBasisIndex R₀ B.gg) (x : B.gg ⊗[R₀] M) :
    B.coordK M' k (LinearMap.lTensor B.gg f x) = f (B.coordK M k x) := by sorry
