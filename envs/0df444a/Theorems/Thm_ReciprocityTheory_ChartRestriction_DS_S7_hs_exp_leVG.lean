-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_exp_leVG
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.hs_exp_leVG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:49.200014+00:00
-- url     : https://prove2.me/theorems/68718aab-e503-4f72-b671-2a645fe8fd3f
-- title:
--   S7: hs exp le VG
-- statement:
--   The S7 construction uses the hs exp le VG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IntegrableOfDecayVG.lean#L278-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IntegrableOfDecayVG.lean#L278-L287

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.hs_exp_leVG (X : Matrix (Fin n) (Fin n) ℂ) :
    hs (NormedSpace.exp X) ≤ n * Real.exp (2 * Real.sqrt (hs X)) := by sorry
