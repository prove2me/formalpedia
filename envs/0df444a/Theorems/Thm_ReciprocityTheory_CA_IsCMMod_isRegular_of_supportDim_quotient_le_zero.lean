-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCMMod_isRegular_of_supportDim_quotient_le_zero
-- name    : ReciprocityTheory.CA.IsCMMod.isRegular_of_supportDim_quotient_le_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:59.276906+00:00
-- url     : https://prove2.me/theorems/f388a27b-f7a9-585d-bdad-289ee4b88552
-- title:
--   Is CMMod: is Regular of support Dim quotient le zero
-- statement:
--   The Is CMMod construction uses the is Regular of support Dim quotient le zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Unmixed.lean#L257-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Unmixed.lean#L257-L325

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

theorem ReciprocityTheory.CA.IsCMMod.isRegular_of_supportDim_quotient_le_zero (h : IsCMMod R M) (xs : List R)
    (hxs : ∀ r ∈ xs, r ∈ maximalIdeal R) (hlen : (xs.length : WithBot ℕ∞) = Module.supportDim R M)
    (h0 : Module.supportDim R (M ⧸ Ideal.ofList xs • (⊤ : Submodule R M)) ≤ 0) :
    IsRegular M xs := by sorry
