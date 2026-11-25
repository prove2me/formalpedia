-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_sm_ker_surj
-- name    : ReciprocityTheory.PGsh.sm_ker_surj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:09:45.432431+00:00
-- url     : https://prove2.me/theorems/ad4897b0-9a16-465a-bc46-557b66dd6859
-- title:
--   PGsh: sm ker surj
-- statement:
--   The PGsh construction uses the sm ker surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L181-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L181-L200

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
variable {ξ : (R' : Type u)} (hsurj : Function.Surjective π.1)
  (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)

theorem ReciprocityTheory.PGsh.sm_ker_surj :
    Function.Surjective ((sm π Dp ξ hsurj hker hsq).1.toLinearMap.restrict
      (sm_ker π Dp hsurj hker hsq)) := by sorry
