-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_tt_prodS
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.tt_prodS
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:55:22.490519+00:00
-- url     : https://prove2.me/theorems/d8e7e887-0e12-5146-be15-5249a4a89d6d
-- title:
--   BL: tt prod S
-- statement:
--   The BL construction uses the tt prod S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LevelDeterminantOfTriangularChange.lean#L168-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LevelDeterminantOfTriangularChange.lean#L168-L180

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
variable (τ : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℂ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.tt_prodS (a : Fin (r' + 1)) :
    ∏ j ∈ Finset.Iic (su a), ‖tt τ j j‖ ^ 2 = ∏ j ∈ Finset.Iic a, ‖τ j j‖ ^ 2 := by sorry
