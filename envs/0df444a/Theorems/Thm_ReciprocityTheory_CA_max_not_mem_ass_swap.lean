-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_max_not_mem_ass_swap
-- name    : ReciprocityTheory.CA.max_not_mem_ass_swap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:35.955908+00:00
-- url     : https://prove2.me/theorems/d0e2d762-3697-41cd-9573-0add82f523a5
-- title:
--   CA: max not mem ass swap
-- statement:
--   The CA construction uses the max not mem ass swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L74-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L74-L90

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

theorem ReciprocityTheory.CA.max_not_mem_ass_swap {x y w : R} (hy : y ∈ maximalIdeal R) (rx : IsSMulRegular M x)
    (ry : IsSMulRegular M y) (hw : w ∈ maximalIdeal R) (rw : IsSMulRegular (QuotSMulTop y M) w) :
    maximalIdeal R ∉ associatedPrimes R (QuotSMulTop x M) := by sorry
