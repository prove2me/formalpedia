-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_isCM_of_isRegularLocalRing
-- name    : ReciprocityTheory.CA.isCM_of_isRegularLocalRing
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:20.877871+00:00
-- url     : https://prove2.me/theorems/9c6701c8-349d-4edf-961a-8b87c1b91d47
-- title:
--   CA: is CM of is Regular Local Ring
-- statement:
--   The CA construction uses the is CM of is Regular Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/IsCMOfIsRegularLocalRing.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/IsCMOfIsRegularLocalRing.lean#L8-L15

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RegGens
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_IsCMOfIsRegularLocalRing
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

theorem ReciprocityTheory.CA.isCM_of_isRegularLocalRing (R : Type*) [CommRing R] [IsRegularLocalRing R] : IsCM R := by sorry
