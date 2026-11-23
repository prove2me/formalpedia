-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fa1Mono_continuous
-- name    : ReciprocityTheory.ChartRestriction.G.I2.fa1Mono_continuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:18.220307+00:00
-- url     : https://prove2.me/theorems/989b32d8-67c9-4762-8bef-cc6f6634f588
-- title:
--   I2: fa1 Mono continuous
-- statement:
--   The I2 construction uses the fa1 Mono continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L16-L19

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

theorem ReciprocityTheory.ChartRestriction.G.I2.fa1Mono_continuous {g : ℕ} (α : Fin g →₀ ℕ) : Continuous (monomialOfMultiindex α) := by sorry
