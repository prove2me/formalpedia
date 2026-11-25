-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_exists_regular_sequence_cons
-- name    : ReciprocityTheory.CA.exists_regular_sequence_cons
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:19.945813+00:00
-- url     : https://prove2.me/theorems/6a5d0a1f-53c6-5b20-996d-053da9f2bc87
-- title:
--   CA: exists regular sequence cons
-- statement:
--   The CA construction uses the exists regular sequence cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L105-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L105-L154

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
variable [IsNoetherianRing R]
universe u in

theorem ReciprocityTheory.CA.exists_regular_sequence_cons (n : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N] {x : R},
      x ∈ maximalIdeal R → IsSMulRegular N x → ModDepthGE R N (n + 1) →
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular N (x :: rs) := by sorry
