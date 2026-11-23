-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paD_smul
-- name    : ReciprocityTheory.ChartRestriction.G.I2.paD_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:43.62997+00:00
-- url     : https://prove2.me/theorems/b9473d7d-5620-4727-bc7c-580faf7519e6
-- title:
--   I2: pa D smul
-- statement:
--   The I2 construction uses the pa D smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L199-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L199-L201

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paD_smul

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
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.paD_smul (α : ι →₀ ℕ) (a : ℂ) {H : EuclideanSpace ℂ ι → ℂ}
    (h : ContDiff ℂ (⊤ : ℕ∞) H) : paD α (a • H) = a * paD α H := by sorry
