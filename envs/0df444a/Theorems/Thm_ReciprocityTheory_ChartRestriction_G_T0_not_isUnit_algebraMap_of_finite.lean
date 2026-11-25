-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_not_isUnit_algebraMap_of_finite
-- name    : ReciprocityTheory.ChartRestriction.G.T0.not_isUnit_algebraMap_of_finite
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:43.447555+00:00
-- url     : https://prove2.me/theorems/3700dda4-40c6-4ba6-bd6e-50a968b91c58
-- title:
--   T0: not is Unit algebra Map of finite
-- statement:
--   The T0 construction uses the not is Unit algebra Map of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegHorPf.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegHorPf.lean#L7-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegAVpt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegHorPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing

theorem ReciprocityTheory.ChartRestriction.G.T0.not_isUnit_algebraMap_of_finite {O V : Type} [CommRing O] [IsLocalRing O] [CommRing V]
    [Nontrivial V] [Algebra O V] [Module.Finite O V] (π : O) (hπ : π ∈ maximalIdeal O) :
    ¬ IsUnit (algebraMap O V π) := by sorry
