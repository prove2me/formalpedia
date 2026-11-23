-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_one_sub
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.dm_one_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:51.731348+00:00
-- url     : https://prove2.me/theorems/945caa6f-7990-4a34-be82-4bf1903478d7
-- title:
--   S7: dm one sub
-- statement:
--   The S7 construction uses the dm one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecMomentsA.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecMomentsA.lean#L56-L62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA
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

theorem ReciprocityTheory.ChartRestriction.DS.S7.dm_one_sub {i : ℕ} (hi : i ≤ n) (a b : Fin i) :
    (1 : Matrix (Fin n) (Fin n) ℂ) (Fin.castLE hi a) (Fin.castLE hi b) = (1 : Matrix (Fin i) (Fin i) ℂ) a b := by sorry
