-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inhV_X_mem
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_X_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:25.609328+00:00
-- url     : https://prove2.me/theorems/98161dd5-dec8-43ae-bf8a-7074cb338b03
-- title:
--   I1: inh V X mem
-- statement:
--   The I1 construction uses the inh V X mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L199-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L199-L200

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_X_mem {s : σ} (h : s ∈ S) : (X s : MvPolynomial σ F) ∈ inhV F S := by sorry
