-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_height_add_of_sphere
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_height_add_of_sphere
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:01.1468+00:00
-- url     : https://prove2.me/theorems/f4d72b47-1766-5082-86b8-0caaf6bc1111
-- title:
--   Multiplicative Heights: gauss height add of sphere
-- statement:
--   The Multiplicative Heights construction uses the gauss height add of sphere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LagrangeIdealLiftsFact.lean#L133-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LagrangeIdealLiftsFact.lean#L133-L144

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory NumberField

theorem ReciprocityTheory.MultiplicativeHeights.gauss_height_add_of_sphere (hInt : SphereLogIntegrableStatement) : HeightAdditiveStatement := by sorry
