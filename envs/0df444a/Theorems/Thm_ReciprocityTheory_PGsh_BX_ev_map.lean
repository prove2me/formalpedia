-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_ev_map
-- name    : ReciprocityTheory.PGsh.BX.ev_map
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:48.836672+00:00
-- url     : https://prove2.me/theorems/599e7b03-11bd-52df-9be1-1832c0b7400b
-- title:
--   BX: ev map
-- statement:
--   The BX construction uses the ev map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/OneAddPowOfSq.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/OneAddPowOfSq.lean#L13-L21

import Definitions.Def_ReciprocityTheory_DualLattices_NsetExpInjectiveSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_OneAddPowOfSq
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

theorem ReciprocityTheory.PGsh.BX.ev_map (B : BX R₀) {R S : LAlg R₀} (f : (R : Type u) →ₐ[R₀] (S : Type u))
    (h : B.gg →ₗ[R₀] (R : Type u)) (v : B.gg ⊗[R₀] (R : Type u)) :
    f (B.ev h v) = B.ev (f.toLinearMap ∘ₗ h) (LinearMap.lTensor B.gg f.toLinearMap v) := by sorry
