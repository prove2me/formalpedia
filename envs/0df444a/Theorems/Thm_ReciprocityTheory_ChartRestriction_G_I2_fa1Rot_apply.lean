-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fa1Rot_apply
-- name    : ReciprocityTheory.ChartRestriction.G.I2.fa1Rot_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:19.6058+00:00
-- url     : https://prove2.me/theorems/61ff5bc2-d037-4fc1-9d48-85fb73741a61
-- title:
--   I2: fa1 Rot apply
-- statement:
--   The I2 construction uses the fa1 Rot apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L126-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L126-L131

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory

theorem ReciprocityTheory.ChartRestriction.G.I2.fa1Rot_apply {g : ℕ} (j : Fin g) (u : Circle) (z : EuclideanSpace ℂ (Fin g)) (i : Fin g) :
    coordinateRotation j u z i = (if i = j then (u : ℂ) else 1) * z i := by sorry
