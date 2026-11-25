-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_minimalPrimes_top
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.inh_minimalPrimes_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:42.740483+00:00
-- url     : https://prove2.me/theorems/00fa4487-d9d3-4eb4-9b01-9cdc844de3a4
-- title:
--   I1: inh minimal Primes top
-- statement:
--   The I1 construction uses the inh minimal Primes top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L74-L79

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
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.inh_minimalPrimes_top : (⊤ : Ideal R).minimalPrimes = ∅ := by sorry
