-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_Ye
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.dm_Ye
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:12:26.341342+00:00
-- url     : https://prove2.me/theorems/ff955753-accf-4a87-82e0-0eda1d4e9557
-- title:
--   S7: dm Ye
-- statement:
--   The S7 construction uses the dm Ye property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecMomentsB.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecMomentsB.lean#L24-L26

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.dm_Ye (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (a b : Fin n) :
    Y a b = ∑ j, U a j * (y j : ℂ) * star (U b j) := by sorry
