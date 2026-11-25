-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCMMod_quotient_ofList
-- name    : ReciprocityTheory.CA.IsCMMod.quotient_ofList
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:50.523643+00:00
-- url     : https://prove2.me/theorems/11327131-1cd0-4b42-9751-205a9ed32944
-- title:
--   Is CMMod: quotient of List
-- statement:
--   The Is CMMod construction uses the quotient of List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Unmixed.lean#L220-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Unmixed.lean#L220-L233

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

theorem ReciprocityTheory.CA.IsCMMod.quotient_ofList (h : IsCMMod R M) {rs : List R}
    (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R) (reg : IsRegular M rs) :
    IsCMMod R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) := by sorry
