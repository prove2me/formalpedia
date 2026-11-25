-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_exists_isRegular_cons_of_modDepthGE
-- name    : ReciprocityTheory.CA.exists_isRegular_cons_of_modDepthGE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:38.46664+00:00
-- url     : https://prove2.me/theorems/1f18d9e6-07b4-4aae-b7e2-be29657986b6
-- title:
--   CA: exists is Regular cons of mod Depth GE
-- statement:
--   The CA construction uses the exists is Regular cons of mod Depth GE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L160-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L160-L163

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

theorem ReciprocityTheory.CA.exists_isRegular_cons_of_modDepthGE {x : R} (hx : x ∈ maximalIdeal R)
    (reg : IsSMulRegular M x) {n : ℕ} (h : ModDepthGE R M (n + 1)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular M (x :: rs) := by sorry
