-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fm_fourCoeff
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fm_fourCoeff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:35.963381+00:00
-- url     : https://prove2.me/theorems/3a5210fa-baa0-55a1-bf05-4ef8644dcad9
-- title:
--   Y: fm four Coeff
-- statement:
--   The Y construction uses the fm four Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourMul.lean#L87-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourMul.lean#L87-L106

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ComplexConjugate
noncomputable section
attribute [local instance] ReciprocityTheory.L2DbarEstimates.Y._p2m_local_instance_19aabe418c_38
attribute [local instance] ReciprocityTheory.L2DbarEstimates.Y._p2m_local_instance_19aabe418c_40

theorem ReciprocityTheory.L2DbarEstimates.Y.fm_fourCoeff {f : ℕ} (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ)
    (hper : ∀ x (n : Fin f → ℤ), fmLine h b (x + fun i => (n i : ℝ)) = fmLine h b x)
    (ν : Fin f → ℤ) :
    fourCoeff h b ν = Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)) *
      UnitAddTorus.mFourierCoeff (fsFun (fmLine h b)) ν := by sorry
