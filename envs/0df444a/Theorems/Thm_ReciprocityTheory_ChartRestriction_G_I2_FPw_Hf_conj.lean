-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_conj
-- name    : ReciprocityTheory.ChartRestriction.G.I2.FPw.Hf_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:45.830943+00:00
-- url     : https://prove2.me/theorems/513d1374-4db3-4580-b4df-f8f958cfd5d5
-- title:
--   FPw: Hf conj
-- statement:
--   The FPw construction uses the Hf conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/HfNegRight.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/HfNegRight.lean#L23-L25

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

theorem ReciprocityTheory.ChartRestriction.G.I2.FPw.Hf_conj (x y : EuclideanSpace ℂ ι) : (starRingEnd ℂ) (Hf x y) = Hf y x := by sorry
