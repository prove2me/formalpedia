-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ccb_inUJ_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.ccb_inUJ_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:45:13.15313+00:00
-- url     : https://prove2.me/theorems/8aa3bef4-b3a7-4e88-8f01-d30907427c83
-- title:
--   S7: ccb in UJ mul
-- statement:
--   The S7 construction uses the ccb in UJ mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainB.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainB.lean#L103-L109

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.ccb_inUJ_mul (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (hh : inUJ ε h) : inUJ ε (g * h) := by sorry
