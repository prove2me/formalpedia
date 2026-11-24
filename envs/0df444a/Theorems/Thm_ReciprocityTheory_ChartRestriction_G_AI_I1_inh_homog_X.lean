-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_homog_X
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.inh_homog_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:50.173928+00:00
-- url     : https://prove2.me/theorems/41fefcd4-85d7-4d74-8e66-bee74cf0680c
-- title:
--   I1: inh homog X
-- statement:
--   The I1 construction uses the inh homog X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L248-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L248-L249

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.inh_homog_X (p : Σ k, ι k) : IsMultiHomog (X p : MRingOver F ι) (Pi.single p.1 1) := by sorry
