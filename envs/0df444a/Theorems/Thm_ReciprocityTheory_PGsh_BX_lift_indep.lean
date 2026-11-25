-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_lift_indep
-- name    : ReciprocityTheory.PGsh.BX.lift_indep
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:05:58.512994+00:00
-- url     : https://prove2.me/theorems/3e770684-7a5a-5310-8dc0-7d9685ab9ca4
-- title:
--   BX: lift indep
-- statement:
--   The BX construction uses the lift indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulKerZero.lean#L74-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulKerZero.lean#L74-L91

import Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulKerZero
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

theorem ReciprocityTheory.PGsh.BX.lift_indep (Tw : ATower R₀ p) (n : ℕ) (th th' : B.G (Tw.R' n)) (w w' : B.gg ⊗[R₀] (Tw.R' n : Type u))
    (he : B.map (Tw.π n) th = B.map (Tw.π n) th')
    (hw : (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w))
    (hw' : (p ^ (n + 1)) • th' = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w')) :
    LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w = LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w' := by sorry
