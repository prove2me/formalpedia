-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_sm_comp____a42742269e01
-- name    : P2M_ReciprocityTheory_PGsh_sm_comp____a42742269e01
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:18:23.957808+00:00
-- url     : https://prove2.me/theorems/331928da-f6fe-5ebe-876d-b80326db55b8
-- title:
--   P2 M Reciprocity Theory PGsh sm comp    a42742269e01: P2 M Reciprocity Theory PGsh sm comp    a42742269e01
-- statement:
--   The P2 M Reciprocity Theory PGsh sm comp    a42742269e01 construction uses the P2 M Reciprocity Theory PGsh sm comp    a42742269e01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L134-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L134-L141

import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
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
variable {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R)

theorem P2M_ReciprocityTheory_PGsh_sm_comp____a42742269e01 {ξ : (R' : Type u)} (hsurj : Function.Surjective π.1)
    (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0) :
    (sm π Dp ξ hsurj hker hsq).comp (ι₁ π Dp) = LHom.id R' := by sorry

alias «ReciprocityTheory».«PGsh».«sm_comp_ι₁» := P2M_ReciprocityTheory_PGsh_sm_comp____a42742269e01
