-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_sum_fin_one_add_eq_add_sum
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.sum_fin_one_add_eq_add_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:51:12.887008+00:00
-- url     : https://prove2.me/theorems/f6c0998f-0b07-5aed-a67c-4231e5ab9e26
-- title:
--   BL: sum fin one add eq add sum
-- statement:
--   The BL construction uses the sum fin one add eq add sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormLiftVecFirstVector.lean#L184-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormLiftVecFirstVector.lean#L184-L190

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.sum_fin_one_add_eq_add_sum {M : Type} [AddCommMonoid M] (F : Fin (1 + r') → M) :
    ∑ a, F a = F ⟨0, by omega⟩ + ∑ a' : Fin r', F ⟨a'.val + 1, by omega⟩ := by sorry
