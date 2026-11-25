-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_inv_sqrt_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.tof_inv_sqrt_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:52:33.507973+00:00
-- url     : https://prove2.me/theorems/efbaa7ae-ce0c-4671-83c3-523286f62dc3
-- title:
--   I2: tof inv sqrt le
-- statement:
--   The I2 construction uses the tof inv sqrt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ShortVectorBoundLeKappa.lean#L35-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ShortVectorBoundLeKappa.lean#L35-L131

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofCovolLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ShortVectorBoundLeKappa
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

theorem ReciprocityTheory.ChartRestriction.G.I2.tof_inv_sqrt_le [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hph : 0 < P.ph) (n : ℕ)
    (hn : n ≤ dstar (E := E) P.m) (c : ℝ) (hc : 0 < c)
    (h1 : 1 ≤ c * Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ n) :
    1 / Real.sqrt (c * (2 : ℝ) ^ (-(n : ℝ) / 2)) ≤
      Real.exp (dstar (E := E) P.m) * (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) := by sorry
