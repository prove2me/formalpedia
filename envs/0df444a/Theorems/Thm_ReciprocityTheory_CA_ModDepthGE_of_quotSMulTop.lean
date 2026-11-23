-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_of_quotSMulTop
-- name    : ReciprocityTheory.CA.ModDepthGE.of_quotSMulTop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:25.041579+00:00
-- url     : https://prove2.me/theorems/56529d84-8926-4a2f-9cf2-d0a551fa11de
-- title:
--   Mod Depth GE: of quot SMul Top
-- statement:
--   The Mod Depth GE construction uses the of quot SMul Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L21-L28

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

theorem ReciprocityTheory.CA.ModDepthGE.of_quotSMulTop {x : R} (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x)
    {n : ℕ} (h : ModDepthGE R (QuotSMulTop x M) n) : ModDepthGE R M (n + 1) := by sorry
