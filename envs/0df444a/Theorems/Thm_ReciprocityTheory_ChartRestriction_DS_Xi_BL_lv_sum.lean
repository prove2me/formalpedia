-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_lv_sum
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.lv_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:46:58.210994+00:00
-- url     : https://prove2.me/theorems/2ff80579-0f11-59a0-ac1f-1d852c46ae89
-- title:
--   BL: lv sum
-- statement:
--   The BL construction uses the lv sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LevelDeterminantOfTriangularChange.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LevelDeterminantOfTriangularChange.lean#L52-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {k r' : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.lv_sum {ι : Type} (s : Finset ι) (f : ι → Fin (2 * r' + k + 1) → ℂ) :
    liftVec k 1 r' (∑ i ∈ s, f i) = ∑ i ∈ s, liftVec k 1 r' (f i) := by sorry
