-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_range_toM
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.range_toM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:48.512162+00:00
-- url     : https://prove2.me/theorems/827af859-317b-43f3-a895-4adeb263eef5
-- title:
--   S7: range to M
-- statement:
--   The S7 construction uses the range to M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IsClosedEmbeddingToM.lean#L80-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IsClosedEmbeddingToM.lean#L80-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.range_toM (ε : Fin n → Bool) : Set.range (fun g : UJ ε => toM g) = {g | inUJ ε g} := by sorry
