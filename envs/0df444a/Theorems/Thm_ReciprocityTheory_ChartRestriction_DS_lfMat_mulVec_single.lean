-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfMat_mulVec_single
-- name    : ReciprocityTheory.ChartRestriction.DS.lfMat_mulVec_single
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:53:51.420477+00:00
-- url     : https://prove2.me/theorems/7ef25f8e-d9cb-4503-888f-ce873c426b36
-- title:
--   DS: lf Mat mul Vec single
-- statement:
--   The DS construction uses the lf Mat mul Vec single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L151-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L151-L162

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

theorem ReciprocityTheory.ChartRestriction.DS.lfMat_mulVec_single (ε : Fin n → Bool) (a b : Fin n) (S : LfIdx ε) (c : ℂ)
    (h : sgE ε cpFock cmFock a b (fockBasis n S.1) = c • fockBasis n S.1) :
    lfMat ε a b *ᵥ Pi.single S 1 = c • Pi.single S 1 := by sorry
