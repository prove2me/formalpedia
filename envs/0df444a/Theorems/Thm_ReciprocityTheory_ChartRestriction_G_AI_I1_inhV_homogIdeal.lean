-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inhV_homogIdeal
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_homogIdeal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:44.187788+00:00
-- url     : https://prove2.me/theorems/59c24e4e-b4bf-4363-9e16-a42d187d442c
-- title:
--   I1: inh V homog Ideal
-- statement:
--   The I1 construction uses the inh V homog Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L259-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L259-L260

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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*}
  [Field F]
variable [DecidableEq (Σ k, ι k)]

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_homogIdeal (S : Finset (Σ k, ι k)) : IsMultiHomogIdeal (inhV F S) := by sorry
