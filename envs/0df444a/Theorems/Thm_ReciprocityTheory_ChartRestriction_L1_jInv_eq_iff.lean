-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_jInv_eq_iff
-- name    : ReciprocityTheory.ChartRestriction.L1.jInv_eq_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:10:29.491711+00:00
-- url     : https://prove2.me/theorems/143ac0a7-51ec-4582-8323-12cbf59e7966
-- title:
--   L1: j Inv eq iff
-- statement:
--   The L1 construction uses the j Inv eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedValA.lean#L55-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedValA.lean#L55-L65

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

theorem ReciprocityTheory.ChartRestriction.L1.jInv_eq_iff (L : PeriodPair) : jInv L = 1728 ↔ L.g₃ = 0 := by sorry
