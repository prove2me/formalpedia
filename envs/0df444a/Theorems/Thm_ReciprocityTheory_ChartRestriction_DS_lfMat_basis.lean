-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfMat_basis
-- name    : ReciprocityTheory.ChartRestriction.DS.lfMat_basis
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:59.192107+00:00
-- url     : https://prove2.me/theorems/17761f80-82cb-57cc-bb92-9f1fb3e421a1
-- title:
--   DS: lf Mat basis
-- statement:
--   The DS construction uses the lf Mat basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L134-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L134-L149

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

theorem ReciprocityTheory.ChartRestriction.DS.lfMat_basis (ε : Fin n → Bool) (a b : Fin n) (S : LfIdx ε) :
    sgE ε cpFock cmFock a b (fockBasis n S.1) = ∑ T : LfIdx ε, lfMat ε a b T S • fockBasis n T.1 := by sorry
