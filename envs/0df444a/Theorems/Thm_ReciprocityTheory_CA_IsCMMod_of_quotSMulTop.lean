-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCMMod_of_quotSMulTop
-- name    : ReciprocityTheory.CA.IsCMMod.of_quotSMulTop
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:39:00.83372+00:00
-- url     : https://prove2.me/theorems/338a4b5b-1c1e-5f28-9c01-223ef0da4551
-- title:
--   Is CMMod: of quot SMul Top
-- statement:
--   The Is CMMod construction uses the of quot SMul Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Unmixed.lean#L168-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Unmixed.lean#L168-L182

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_of_quotSMulTop

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

theorem ReciprocityTheory.CA.IsCMMod.of_quotSMulTop [IsNoetherianRing R] [Module.Finite R M] {x : R}
    (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x) (h : IsCMMod R (QuotSMulTop x M)) :
    IsCMMod R M := by sorry
