-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCMMod_quotSMulTop
-- name    : ReciprocityTheory.CA.IsCMMod.quotSMulTop
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:10.019313+00:00
-- url     : https://prove2.me/theorems/53f48646-b618-4a05-b498-e94d1c000882
-- title:
--   Is CMMod: quot SMul Top
-- statement:
--   The Is CMMod construction uses the quot SMul Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Unmixed.lean#L152-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Unmixed.lean#L152-L166

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_quotSMulTop

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

theorem ReciprocityTheory.CA.IsCMMod.quotSMulTop (h : IsCMMod R M) {x : R} (hx : x ∈ maximalIdeal R)
    (reg : IsSMulRegular M x) : IsCMMod R (QuotSMulTop x M) := by sorry
