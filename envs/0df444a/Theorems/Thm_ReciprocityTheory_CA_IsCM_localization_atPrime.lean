-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCM_localization_atPrime
-- name    : ReciprocityTheory.CA.IsCM.localization_atPrime
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:38.513266+00:00
-- url     : https://prove2.me/theorems/5abcac7f-5780-4be8-a313-e257c5bb239e
-- title:
--   Is CM: localization at Prime
-- statement:
--   The Is CM construction uses the localization at Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/LocDim.lean#L55-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/LocDim.lean#L55-L70

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
variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem ReciprocityTheory.CA.IsCM.localization_atPrime (h : IsCM R) (P : Ideal R) [P.IsPrime] :
    IsCM (Localization.AtPrime P) := by sorry
