-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_socle_of_max_mem_ass
-- name    : ReciprocityTheory.CA.socle_of_max_mem_ass
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:14.362137+00:00
-- url     : https://prove2.me/theorems/4f12770c-7ca2-4d1c-9a42-59f6d63bb9bc
-- title:
--   CA: socle of max mem ass
-- statement:
--   The CA construction uses the socle of max mem ass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L54-L65

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

theorem ReciprocityTheory.CA.socle_of_max_mem_ass {N : Type*} [AddCommGroup N] [Module R N]
    (h : maximalIdeal R ∈ associatedPrimes R N) :
    ∃ a : N, a ≠ 0 ∧ ∀ z ∈ maximalIdeal R, z • a = 0 := by sorry
