-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ccb_inG_cpart1
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.ccb_inG_cpart1
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:24.961801+00:00
-- url     : https://prove2.me/theorems/bf175d84-c119-54e3-8e5d-2bda02c6f616
-- title:
--   S7: ccb in G cpart1
-- statement:
--   The S7 construction uses the ccb in G cpart1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainB.lean#L32-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainB.lean#L32-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.ccb_inG_cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart1 ε Z) := by sorry
