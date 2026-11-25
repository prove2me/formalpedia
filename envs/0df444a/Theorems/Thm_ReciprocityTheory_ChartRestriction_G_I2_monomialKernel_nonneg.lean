-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_monomialKernel_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.I2.monomialKernel_nonneg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:33.177535+00:00
-- url     : https://prove2.me/theorems/7c0296bd-a39b-42ff-8dd0-db33fe1c2fb2
-- title:
--   I2: monomial Kernel nonneg
-- statement:
--   The I2 construction uses the monomial Kernel nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegralMulConjGaussianEqCoeffNormSq.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegralMulConjGaussianEqCoeffNormSq.lean#L25-L28

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

theorem ReciprocityTheory.ChartRestriction.G.I2.monomialKernel_nonneg {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) :
    0 ≤ fa1K p z := by sorry
