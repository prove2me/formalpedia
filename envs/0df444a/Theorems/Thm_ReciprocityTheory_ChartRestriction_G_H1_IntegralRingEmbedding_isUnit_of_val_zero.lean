-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_isUnit_of_val_zero
-- name    : ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.isUnit_of_val_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:51:28.855191+00:00
-- url     : https://prove2.me/theorems/95d0ac9b-6570-45f4-9369-24cb440e27d9
-- title:
--   Integral Ring Embedding: is Unit of val zero
-- statement:
--   The Integral Ring Embedding construction uses the is Unit of val zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IntegralRingEmbedding.lean#L52-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IntegralRingEmbedding.lean#L52-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IntegralRingEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
open Module
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.isUnit_of_val_zero (x : intRing v) (hx : v (x : F) = 0) : IsUnit x := by sorry
