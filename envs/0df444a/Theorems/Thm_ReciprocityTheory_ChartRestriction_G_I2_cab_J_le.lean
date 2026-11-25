-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_J_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cab_J_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:31.401149+00:00
-- url     : https://prove2.me/theorems/821ba8c0-2c1c-43b3-b776-462d0064f15a
-- title:
--   I2: cab J le
-- statement:
--   The I2 construction uses the cab J le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L43-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L43-L90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.I2.cab_J_le (η : EuclideanSpace ℂ ι) (hη : ‖η‖ ≤ 1) (c q : ℕ) (hq : 1 ≤ q) :
    ∫ v : EuclideanSpace ℂ ι, ‖MvPolynomial.eval (fun i => v i) (cabPoly η c)‖ ^ 2 *
      Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤
      c.factorial * (2 / (q * Real.pi)) ^ c * (2 / q) ^ Fintype.card ι := by sorry
