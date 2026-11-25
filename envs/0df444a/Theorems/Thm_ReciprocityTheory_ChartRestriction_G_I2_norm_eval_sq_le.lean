-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_norm_eval_sq_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.norm_eval_sq_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:54.546221+00:00
-- url     : https://prove2.me/theorems/83ea22bd-a6da-42f3-9fa6-6ba2c463b5c6
-- title:
--   I2: norm eval sq le
-- statement:
--   The I2 construction uses the norm eval sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegralMulConjGaussianEqCoeffNormSq.lean#L41-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegralMulConjGaussianEqCoeffNormSq.lean#L41-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
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

theorem ReciprocityTheory.ChartRestriction.G.I2.norm_eval_sq_le {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) :
    ‖MvPolynomial.eval (fun i => z i) p‖ ^ 2 ≤ fa1N p * fa1K p z := by sorry
