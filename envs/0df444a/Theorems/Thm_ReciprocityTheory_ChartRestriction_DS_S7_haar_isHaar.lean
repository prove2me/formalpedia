-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_haar_isHaar
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.haar_isHaar
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:45:38.455794+00:00
-- url     : https://prove2.me/theorems/5e5d149a-e3ee-466b-88bd-8cc218a079c9
-- title:
--   S7: haar is Haar
-- statement:
--   The S7 construction uses the haar is Haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IsClosedEmbeddingToM.lean#L107-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IsClosedEmbeddingToM.lean#L107-L107

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.haar_isHaar (ε : Fin n → Bool) : (Measure.haar : Measure (UJ ε)).IsHaarMeasure := by sorry
