-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_mat_conj_hasDerivAt
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.mat_conj_hasDerivAt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:55:28.109037+00:00
-- url     : https://prove2.me/theorems/5f623ee0-d078-4629-a1b9-8408224d5ce0
-- title:
--   HW: mat conj has Deriv At
-- statement:
--   The HW construction uses the mat conj has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L128-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L128-L134

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem ReciprocityTheory.ChartRestriction.DS.HW.mat_conj_hasDerivAt (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun z : ℂ => NormedSpace.exp (z • X) * Y * NormedSpace.exp (z • (-X)))
      (X * Y - Y * X) ((0 : ℝ) : ℂ) := by sorry
