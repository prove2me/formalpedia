-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_toMatrix_cp
-- name    : ReciprocityTheory.ChartRestriction.DS.lf_toMatrix_cp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:03.62182+00:00
-- url     : https://prove2.me/theorems/2b29066c-1ced-537e-b1c2-7695c8e8b891
-- title:
--   DS: lf to Matrix cp
-- statement:
--   The DS construction uses the lf to Matrix cp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L26-L27

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

theorem ReciprocityTheory.ChartRestriction.DS.lf_toMatrix_cp (i a : Fin n) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpFock i a) = lfP i a := by sorry
