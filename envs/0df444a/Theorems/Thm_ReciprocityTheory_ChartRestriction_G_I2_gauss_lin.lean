-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_gauss_lin
-- name    : ReciprocityTheory.ChartRestriction.G.I2.gauss_lin
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:33.383845+00:00
-- url     : https://prove2.me/theorems/9145c980-6c64-45f1-b44c-c8426aa0957c
-- title:
--   I2: gauss lin
-- statement:
--   The I2 construction uses the gauss lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/UnfoldZn.lean#L46-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/UnfoldZn.lean#L46-L107

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CubeIcoMeas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_UnfoldZn
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
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.I2.gauss_lin {d : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (ob : OrthonormalBasis (Fin d) ℝ W) (u b : Fin d → W)
    (hub : ∀ j i, inner ℝ (u j) (b i) = if j = i then (1 : ℝ) else 0) :
    ∫⁻ a : Fin d → ℝ, ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖∑ j, a j • u j‖ ^ 2)) =
      ENNReal.ofReal (|ob.toBasis.det b| * (2 : ℝ) ^ (-(d : ℝ) / 2)) := by sorry
