-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_toMatrix_cm
-- name    : ReciprocityTheory.ChartRestriction.DS.lf_toMatrix_cm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:58:18.601357+00:00
-- url     : https://prove2.me/theorems/3182826c-c2dd-5da4-87b2-b253a93a5d61
-- title:
--   DS: lf to Matrix cm
-- statement:
--   The DS construction uses the lf to Matrix cm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L29-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.lf_toMatrix_cm (i a : Fin n) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cmFock i a) = (lfP i a)ᵀ := by sorry
