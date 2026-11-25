-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_key2
-- name    : ReciprocityTheory.ChartRestriction.G.I2.FPw.key2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:27:56.134878+00:00
-- url     : https://prove2.me/theorems/8db45b43-c494-599a-bd4d-c9101b9a5af8
-- title:
--   FPw: key2
-- statement:
--   The FPw construction uses the key2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaThContinuous.lean#L97-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaThContinuous.lean#L97-L126

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_DetMEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.FPw.key2 (q : ℕ) (γ x : EuclideanSpace ℂ ι) :
    cexp (q * Real.pi * Hf x γ + q * Real.pi * Hf γ γ / 2) * ((paW q (x + γ) : ℝ) : ℂ) =
      ((paW q x : ℝ) : ℂ) * (starRingEnd ℂ) (cexp (q * Real.pi * Hf x (-γ) - q * Real.pi * Hf (-γ) (-γ) / 2)) := by sorry
