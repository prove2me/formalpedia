-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCM_depthGE_localization_of_le_height
-- name    : ReciprocityTheory.CA.IsCM.depthGE_localization_of_le_height
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:37.110541+00:00
-- url     : https://prove2.me/theorems/865131b3-194b-5b9e-8de1-8fc6238427ad
-- title:
--   Is CM: depth GE localization of le height
-- statement:
--   The Is CM construction uses the depth GE localization of le height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/LocDim.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/LocDim.lean#L49-L53

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

theorem ReciprocityTheory.CA.IsCM.depthGE_localization_of_le_height (h : IsCM R) (P : Ideal R) [P.IsPrime] {r : ℕ}
    (hr : (r : ℕ∞) ≤ P.height) : DepthGE (Localization.AtPrime P) r := by sorry
