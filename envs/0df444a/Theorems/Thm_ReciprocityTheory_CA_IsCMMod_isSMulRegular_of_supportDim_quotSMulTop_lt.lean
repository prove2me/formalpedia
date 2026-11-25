-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCMMod_isSMulRegular_of_supportDim_quotSMulTop_lt
-- name    : ReciprocityTheory.CA.IsCMMod.isSMulRegular_of_supportDim_quotSMulTop_lt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:36.611657+00:00
-- url     : https://prove2.me/theorems/558c41de-af58-43f7-96db-81ac1d9764c6
-- title:
--   Is CMMod: is SMul Regular of support Dim quot SMul Top lt
-- statement:
--   The Is CMMod construction uses the is SMul Regular of support Dim quot SMul Top lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Unmixed.lean#L184-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Unmixed.lean#L184-L218

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem ReciprocityTheory.CA.IsCMMod.isSMulRegular_of_supportDim_quotSMulTop_lt (h : IsCMMod R M) {x : R}
    (hd : Module.supportDim R (QuotSMulTop x M) < Module.supportDim R M) :
    IsSMulRegular M x := by sorry
