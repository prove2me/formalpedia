-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_sum_coordK
-- name    : ReciprocityTheory.PGsh.BX.sum_coordK
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:46.439684+00:00
-- url     : https://prove2.me/theorems/88ffed42-d58e-5380-976f-3b5bb993d340
-- title:
--   BX: sum coord K
-- statement:
--   The BX construction uses the sum coord K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsLimTensor.lean#L76-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsLimTensor.lean#L76-L86

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

theorem ReciprocityTheory.PGsh.BX.sum_coordK (M : Type u) [AddCommGroup M] [Module R₀ M] (x : B.gg ⊗[R₀] M) :
    ∑ k, (Module.Free.chooseBasis R₀ B.gg k) ⊗ₜ[R₀] B.coordK M k x = x := by sorry
