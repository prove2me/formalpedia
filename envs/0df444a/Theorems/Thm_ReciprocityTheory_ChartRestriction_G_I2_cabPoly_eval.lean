-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cabPoly_eval
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cabPoly_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:17.381804+00:00
-- url     : https://prove2.me/theorems/56a7c58d-3783-4457-8b31-f09e5b5347ff
-- title:
--   I2: cab Poly eval
-- statement:
--   The I2 construction uses the cab Poly eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L28-L31

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

theorem ReciprocityTheory.ChartRestriction.G.I2.cabPoly_eval (η v : EuclideanSpace ℂ ι) (c : ℕ) :
    MvPolynomial.eval (fun i => v i) (cabPoly η c) = (Hf v η) ^ c := by sorry
