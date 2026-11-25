-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_contDiffOn_powerDet
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.LemK.contDiffOn_powerDet
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:44:45.868094+00:00
-- url     : https://prove2.me/theorems/4708bd53-c831-52ce-b29a-0030aad0e4d6
-- title:
--   Lem K: cont Diff On power Det
-- statement:
--   The Lem K construction uses the cont Diff On power Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/RightHolRightHolEq.lean#L144-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/RightHolRightHolEq.lean#L144-L158

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.LemK.contDiffOn_powerDet (μ : Fin n → ℤ) : ContDiffOn ℂ ∞ (PhiP μ) (OmegaP n) := by sorry
