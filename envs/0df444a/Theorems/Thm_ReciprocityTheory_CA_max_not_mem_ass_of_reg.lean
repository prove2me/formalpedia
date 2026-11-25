-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_max_not_mem_ass_of_reg
-- name    : ReciprocityTheory.CA.max_not_mem_ass_of_reg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:53.719675+00:00
-- url     : https://prove2.me/theorems/ced02627-c3a0-4d3d-a7ba-a8d1ed17bb4e
-- title:
--   CA: max not mem ass of reg
-- statement:
--   The CA construction uses the max not mem ass of reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L67-L72

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

theorem ReciprocityTheory.CA.max_not_mem_ass_of_reg {N : Type*} [AddCommGroup N] [Module R N] {w : R}
    (hw : w ∈ maximalIdeal R) (rw : IsSMulRegular N w) :
    maximalIdeal R ∉ associatedPrimes R N := by sorry
