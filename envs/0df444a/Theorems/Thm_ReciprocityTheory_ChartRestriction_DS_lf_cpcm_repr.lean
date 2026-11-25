-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_cpcm_repr
-- name    : ReciprocityTheory.ChartRestriction.DS.lf_cpcm_repr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:55.409969+00:00
-- url     : https://prove2.me/theorems/b112554a-8cb8-5ada-a91a-34942bdf606f
-- title:
--   DS: lf cpcm repr
-- statement:
--   The DS construction uses the lf cpcm repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L82-L92

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

theorem ReciprocityTheory.ChartRestriction.DS.lf_cpcm_repr {ε : Fin n → Bool} {i a : Fin n} (j b : Fin n) (hia : ε i = true ∧ ε a = false)
    {S T : Finset (Fin (n * n))} (hS : S ⊆ lfPhysModes ε) (hT : ¬ T ⊆ lfPhysModes ε) :
    (fockBasis n).repr ((cpFock i a * cmFock j b) (fockBasis n S)) T = 0 := by sorry
