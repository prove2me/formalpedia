-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCMMod_ringKrullDim_quotient_eq_supportDim
-- name    : ReciprocityTheory.CA.IsCMMod.ringKrullDim_quotient_eq_supportDim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:49.550042+00:00
-- url     : https://prove2.me/theorems/4d15b187-4891-494c-8ee5-8df6f40732a4
-- title:
--   Is CMMod: ring Krull Dim quotient eq support Dim
-- statement:
--   The Is CMMod construction uses the ring Krull Dim quotient eq support Dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Unmixed.lean#L89-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Unmixed.lean#L89-L108

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

theorem ReciprocityTheory.CA.IsCMMod.ringKrullDim_quotient_eq_supportDim (h : IsCMMod R M) {p : Ideal R}
    (hp : p ∈ associatedPrimes R M) : ringKrullDim (R ⧸ p) = Module.supportDim R M := by sorry
