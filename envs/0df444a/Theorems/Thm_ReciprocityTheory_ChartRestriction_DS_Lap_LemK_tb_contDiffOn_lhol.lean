-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_tb_contDiffOn_lhol
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.LemK.tb_contDiffOn_lhol
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:43:22.048833+00:00
-- url     : https://prove2.me/theorems/fb16d898-28f6-4a50-b082-735f55c86bcb
-- title:
--   Lem K: tb cont Diff On lhol
-- statement:
--   The Lem K construction uses the tb cont Diff On lhol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/TransferB.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/TransferB.lean#L80-L85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
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
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ReciprocityTheory.ChartRestriction.DS.Lap.LemK.tb_contDiffOn_lhol {F : Matrix (Fin n) (Fin n) ℂ → E} {s : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hs : IsOpen s) (hF : ContDiffOn ℂ ω F s) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℂ ω (Lhol Z F) s := by sorry
