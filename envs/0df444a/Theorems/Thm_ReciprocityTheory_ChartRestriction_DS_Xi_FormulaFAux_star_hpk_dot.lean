-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_star_hpk_dot
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.star_hpk_dot
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:20:22.702097+00:00
-- url     : https://prove2.me/theorems/0a25453c-96d9-5d3b-b315-3d57e21c9da0
-- title:
--   Formula FAux: star hpk dot
-- statement:
--   The Formula FAux construction uses the star hpk dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermMatrixMulVecFirst.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermMatrixMulVecFirst.lean#L36-L44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermMatrixMulVecFirst
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
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux

theorem ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.star_hpk_dot (k r : ℕ) (u w : Fin (2 * r + k + 1) → ℂ) :
    star (Hpk k r *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ w) = star u ⬝ᵥ w := by sorry
