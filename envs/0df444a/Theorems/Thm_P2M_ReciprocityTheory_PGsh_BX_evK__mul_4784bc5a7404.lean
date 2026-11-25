-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_BX_evK__mul_4784bc5a7404
-- name    : P2M_ReciprocityTheory_PGsh_BX_evK__mul_4784bc5a7404
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:17:39.702453+00:00
-- url     : https://prove2.me/theorems/00b84a54-3442-43c6-a028-1cf176e7213d
-- title:
--   P2 M Reciprocity Theory PGsh BX ev K  mul 4784bc5a7404: P2 M Reciprocity Theory PGsh BX ev K  mul 4784bc5a7404
-- statement:
--   The P2 M Reciprocity Theory PGsh BX ev K  mul 4784bc5a7404 construction uses the P2 M Reciprocity Theory PGsh BX ev K  mul 4784bc5a7404 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/StThmA.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/StThmA.lean#L28-L40

import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatement
import Definitions.Def_ReciprocityTheory_DualLattices_StThmA
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
variable (B : BX R₀)

theorem P2M_ReciprocityTheory_PGsh_BX_evK__mul_4784bc5a7404 {R' R : LAlg R₀} (π : LHom R' R) (ξ : (R' : Type u)) (hξ : ξ ∈ π.ker)
    (h : B.gg →ₗ[R₀] R') (v : B.gg ⊗[R₀] (R' : Type u)) :
    B.evK π h (TensorProduct.map LinearMap.id (ξmul π ξ hξ) v) = ξ * B.ev h v := by sorry

alias «ReciprocityTheory».«PGsh».«BX».«evK_ξmul» := P2M_ReciprocityTheory_PGsh_BX_evK__mul_4784bc5a7404
