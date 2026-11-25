-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_pow_div_factorial_le_choose
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.pow_div_factorial_le_choose
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:59.565769+00:00
-- url     : https://prove2.me/theorems/1b5ee9d6-bb96-50dd-aa82-f928fef91b2d
-- title:
--   Arakelov Geometry: pow div factorial le choose
-- statement:
--   The Arakelov Geometry construction uses the pow div factorial le choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ChooseLePowDivFactorial.lean#L176-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ChooseLePowDivFactorial.lean#L176-L183

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Module Filter Asymptotics
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.pow_div_factorial_le_choose (m D : ℕ) : ((m : ℝ) ^ D) / (D.factorial : ℝ) ≤ ((m + D).choose D : ℝ) := by sorry
