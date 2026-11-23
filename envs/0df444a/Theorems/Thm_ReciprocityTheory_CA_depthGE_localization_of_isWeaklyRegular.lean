-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_depthGE_localization_of_isWeaklyRegular
-- name    : ReciprocityTheory.CA.depthGE_localization_of_isWeaklyRegular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:35.793496+00:00
-- url     : https://prove2.me/theorems/a76691b4-b34a-48bf-bab8-c498a444aff1
-- title:
--   CA: depth GE localization of is Weakly Regular
-- statement:
--   The CA construction uses the depth GE localization of is Weakly Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/LocDim.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/LocDim.lean#L7-L22

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularOfLeHeight
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
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

theorem ReciprocityTheory.CA.depthGE_localization_of_isWeaklyRegular {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime]
    {rs : List R} (hrs : ∀ x ∈ rs, x ∈ P) (reg : IsWeaklyRegular R rs) :
    DepthGE (Localization.AtPrime P) rs.length := by sorry
