-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_length_pow
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:32.586915+00:00
-- url     : https://prove2.me/theorems/d55368f9-1dd1-40c8-b7ea-8b235d361c03
-- title:
--   I1: inh length pow
-- statement:
--   The I1 construction uses the inh length pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L31-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L31-L45

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_pow [IsDomain R] (x : R) (hx : x ≠ 0) [(Ideal.span {x}).IsPrime] (m : ℕ) :
    Module.length (Localization.AtPrime (Ideal.span {x}))
      (Localization.AtPrime (Ideal.span {x}) ⧸
        (Ideal.span {x ^ m}).map (algebraMap R (Localization.AtPrime (Ideal.span {x})))) = m := by sorry
