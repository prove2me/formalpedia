-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurable_logEval
-- name    : ReciprocityTheory.MultiplicativeHeights.measurable_logEval
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:36.743651+00:00
-- url     : https://prove2.me/theorems/4602c167-3d1a-41c6-be6d-25dd8d8bbada
-- title:
--   Multiplicative Heights: measurable log Eval
-- statement:
--   The Multiplicative Heights construction uses the measurable log Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L126-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L126-L127

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.MultiplicativeHeights.measurable_logEval (f : MvPolynomial ι ℂ) :
    Measurable fun θ : ι → ℝ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖ := by sorry
