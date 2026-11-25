-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh___comp_sm_0df11068a3ae
-- name    : P2M_ReciprocityTheory_PGsh___comp_sm_0df11068a3ae
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:09.549419+00:00
-- url     : https://prove2.me/theorems/3b159376-94ca-4c3d-901a-b355a874f434
-- title:
--   P2 M Reciprocity Theory PGsh   comp sm 0df11068a3ae: P2 M Reciprocity Theory PGsh   comp sm 0df11068a3ae
-- statement:
--   The P2 M Reciprocity Theory PGsh   comp sm 0df11068a3ae construction uses the P2 M Reciprocity Theory PGsh   comp sm 0df11068a3ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L114-L119

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
variable {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R) (ξ : (R' : Type u))
  (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)

theorem P2M_ReciprocityTheory_PGsh___comp_sm_0df11068a3ae : π.comp (sm π Dp ξ hsurj hker hsq) = π.comp (FP.p₁ π Dp.π) := by sorry

alias «ReciprocityTheory».«PGsh».«π_comp_sm» := P2M_ReciprocityTheory_PGsh___comp_sm_0df11068a3ae
