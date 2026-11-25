-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_measurable_log_eval_torus
-- name    : ReciprocityTheory.ChartRestriction.G.T0.measurable_log_eval_torus
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:06.30036+00:00
-- url     : https://prove2.me/theorems/26122140-9d35-5ff6-badc-26ac58a70a01
-- title:
--   T0: measurable log eval torus
-- statement:
--   The T0 construction uses the measurable log eval torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ContinuousTorusPoint.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ContinuousTorusPoint.lean#L30-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ContinuousTorusPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed

theorem ReciprocityTheory.ChartRestriction.G.T0.measurable_log_eval_torus {κ : Type} [Fintype κ] (f : MvPolynomial κ ℂ) :
    Measurable (fun θ : κ → ℝ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖) := by sorry
