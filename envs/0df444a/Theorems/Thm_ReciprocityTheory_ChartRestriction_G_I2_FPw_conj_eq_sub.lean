-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_conj_eq_sub
-- name    : ReciprocityTheory.ChartRestriction.G.I2.FPw.conj_eq_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:09:37.879038+00:00
-- url     : https://prove2.me/theorems/8de4e2b6-3314-4d56-9417-0e631b4bc9e1
-- title:
--   FPw: conj eq sub
-- statement:
--   The FPw construction uses the conj eq sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/HfNegRight.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/HfNegRight.lean#L35-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
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

theorem ReciprocityTheory.ChartRestriction.G.I2.FPw.conj_eq_sub (z : ℂ) : (starRingEnd ℂ) z = z - 2 * (z.im : ℂ) * I := by sorry
