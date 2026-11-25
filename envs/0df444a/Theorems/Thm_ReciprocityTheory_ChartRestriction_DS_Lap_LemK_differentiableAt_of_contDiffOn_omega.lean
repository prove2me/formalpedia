-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_differentiableAt_of_contDiffOn_omega
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.LemK.differentiableAt_of_contDiffOn_omega
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:58.034789+00:00
-- url     : https://prove2.me/theorems/1154c9b5-101c-4de3-ad7a-7e5f6332b24d
-- title:
--   Lem K: differentiable At of cont Diff On omega
-- statement:
--   The Lem K construction uses the differentiable At of cont Diff On omega property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/RightHolRightHolEq.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/RightHolRightHolEq.lean#L106-L109

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_RightHolRightHolEq
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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Lap.LemK.differentiableAt_of_contDiffOn_omega {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaP n)) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaP n) :
    DifferentiableAt ℂ F z := by sorry
