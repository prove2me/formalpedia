-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_inP_conj
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.inP_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:07:34.717589+00:00
-- url     : https://prove2.me/theorems/3476ec71-2734-48c1-99f5-0f565125381b
-- title:
--   S7: in P conj
-- statement:
--   The S7 construction uses the in P conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ExpInPPosDef.lean#L135-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ExpInPPosDef.lean#L135-L159

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool}
open PolarDecomposition

theorem ReciprocityTheory.ChartRestriction.DS.S7.inP_conj (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    inP ε (toMK k * X * toMK k⁻¹) ∧
      NormedSpace.exp (toMK k * X * toMK k⁻¹) = toMK k * NormedSpace.exp X * toMK k⁻¹ := by sorry
