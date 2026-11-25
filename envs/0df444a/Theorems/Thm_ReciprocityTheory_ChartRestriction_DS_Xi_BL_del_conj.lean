-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_del_conj
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.del_conj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:46:53.435547+00:00
-- url     : https://prove2.me/theorems/c26315f8-cbad-587d-9e9b-61cca66f1982
-- title:
--   BL: del conj
-- statement:
--   The BL construction uses the del conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LevelDeterminantOfTriangularChange.lean#L211-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LevelDeterminantOfTriangularChange.lean#L211-L237

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.del_conj (hHC : HeisConjLev) (κ : Mat k r') (hκG : κ ∈ GV k r') (hκU : κᴴ * κ = 1) (X : HPar k r')
    (l : Fin (1 + r' + 1)) :
    Del k (1 + r') l (heis0 k r' X * ιLev k 1 r' κ) = Del k (1 + r') l (heis0 k r' (κᴴ *ᵥ X.1, X.2)) := by sorry
