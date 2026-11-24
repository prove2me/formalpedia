-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_avg_fd_prod
-- name    : ReciprocityTheory.ChartRestriction.G.I2.avg_fd_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:49.856442+00:00
-- url     : https://prove2.me/theorems/a865d905-ace5-4466-894d-da609c81dbb1
-- title:
--   I2: avg fd prod
-- statement:
--   The I2 construction uses the avg fd prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/L2NormFundamentalDomain.lean#L82-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/L2NormFundamentalDomain.lean#L82-L93

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
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
variable {E : Type} [Field E] [NumberField E] (X : PT E)

theorem ReciprocityTheory.ChartRestriction.G.I2.avg_fd_prod {n : ℕ} (f : Fin n → Vsp X.dim → ℝ) :
    ⨍ v in X.fd n, ∏ k, f k (v k) = ∏ k, ⨍ x in ZSpan.fundamentalDomain X.b, f k x := by sorry
