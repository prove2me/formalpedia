-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_jInv_eq_zero_iff
-- name    : ReciprocityTheory.ChartRestriction.L1.jInv_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:10:45.459656+00:00
-- url     : https://prove2.me/theorems/22e61425-fc0d-4627-9a10-3718efaca885
-- title:
--   L1: j Inv eq zero iff
-- statement:
--   The L1 construction uses the j Inv eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedValA.lean#L42-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedValA.lean#L42-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HasCMByStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.jInv_eq_zero_iff (L : PeriodPair) : jInv L = 0 ↔ L.g₂ = 0 := by sorry
