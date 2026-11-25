-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ccb_inG_cpart2
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.ccb_inG_cpart2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:45:20.878924+00:00
-- url     : https://prove2.me/theorems/da7f9348-97d8-4d4a-b784-2b1c2ef7b1e5
-- title:
--   S7: ccb in G cpart2
-- statement:
--   The S7 construction uses the ccb in G cpart2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainB.lean#L51-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainB.lean#L51-L72

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.ccb_inG_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart2 ε Z) := by sorry
