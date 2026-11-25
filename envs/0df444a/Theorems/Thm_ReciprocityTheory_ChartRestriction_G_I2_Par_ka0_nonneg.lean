-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Par_ka0_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Par_ka0_nonneg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:23:31.35691+00:00
-- url     : https://prove2.me/theorems/f5509a4e-1098-4e13-a30b-2eda0d3d7d67
-- title:
--   I2: Par ka0 nonneg
-- statement:
--   The I2 construction uses the Par ka0 nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofUMapSqSmul.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofUMapSqSmul.lean#L18-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofUMapSqSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.Par_ka0_nonneg {X : PT E} {DF : ℕ} (P : Par X DF) : 0 ≤ P.ka0 := by sorry
