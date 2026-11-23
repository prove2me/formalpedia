-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_S
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.dm_S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:33.972725+00:00
-- url     : https://prove2.me/theorems/08263d42-34b4-4e1f-9c2a-2fdd7b1aae95
-- title:
--   S7: dm S
-- statement:
--   The S7 construction uses the dm S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecMomentsB.lean#L101-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecMomentsB.lean#L101-L105

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsB
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
variable {n : ℕ}
variable {U Y : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.dm_S (J : Finset (Fin n)) : ((∑ j ∈ J, y j : ℝ) : ℂ) = ∑ k, dmInd J k * (y k : ℂ) := by sorry
