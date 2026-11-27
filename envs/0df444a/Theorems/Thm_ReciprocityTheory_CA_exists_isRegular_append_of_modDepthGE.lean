-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_exists_isRegular_append_of_modDepthGE
-- name    : ReciprocityTheory.CA.exists_isRegular_append_of_modDepthGE
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:03:11.718738+00:00
-- url     : https://prove2.me/theorems/1610633d-74d5-48a1-82fa-1ebbbf18ce81
-- title:
--   CA: exists is Regular append of mod Depth GE
-- statement:
--   The CA construction uses the exists is Regular append of mod Depth GE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L170-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L170-L186

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R M]

theorem ReciprocityTheory.CA.exists_isRegular_append_of_modDepthGE {rs : List R} (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (reg : IsRegular M rs) {n : ℕ} (h : ModDepthGE R M (rs.length + n)) :
    ∃ rs' : List R, rs'.length = n ∧ (∀ r ∈ rs', r ∈ maximalIdeal R) ∧
      IsRegular M (rs ++ rs') := by sorry
