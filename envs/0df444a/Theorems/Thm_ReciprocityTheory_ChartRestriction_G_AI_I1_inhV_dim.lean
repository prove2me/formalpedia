-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inhV_dim
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_dim
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:55.634396+00:00
-- url     : https://prove2.me/theorems/e18debd7-61ec-438d-84de-df1fc96beaf3
-- title:
--   I1: inh V dim
-- statement:
--   The I1 construction uses the inh V dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L206-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L206-L209

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {σ : Type*} (F : Type*) [Field F] [DecidableEq σ] (S : Finset σ)

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_dim [Finite σ] :
    ringKrullDim (MvPolynomial σ F ⧸ inhV F S) = (Nat.card {s // s ∉ S} : WithBot ℕ∞) := by sorry
