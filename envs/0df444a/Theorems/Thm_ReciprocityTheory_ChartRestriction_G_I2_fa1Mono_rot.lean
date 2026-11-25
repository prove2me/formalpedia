-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fa1Mono_rot
-- name    : ReciprocityTheory.ChartRestriction.G.I2.fa1Mono_rot
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:20.683819+00:00
-- url     : https://prove2.me/theorems/462dbee3-8333-46b7-beb0-6205270fa3be
-- title:
--   I2: fa1 Mono rot
-- statement:
--   The I2 construction uses the fa1 Mono rot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L133-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L133-L138

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

theorem ReciprocityTheory.ChartRestriction.G.I2.fa1Mono_rot {g : ℕ} (α : Fin g →₀ ℕ) (j : Fin g) (u : Circle)
    (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α (coordinateRotation j u z) = (u : ℂ) ^ (α j) * monomialOfMultiindex α z := by sorry
