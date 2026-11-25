-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticOffDiagonalBounds_offdiag_le
-- name    : ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds.offdiag_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:29.716076+00:00
-- url     : https://prove2.me/theorems/0be8d3a9-e469-4460-87d2-46c1e94d444c
-- title:
--   Quadratic Off Diagonal Bounds: offdiag le
-- statement:
--   The Quadratic Off Diagonal Bounds construction uses the offdiag le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticOffDiagonalBounds.lean#L44-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticOffDiagonalBounds.lean#L44-L70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticOffDiagonalBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds.offdiag_le {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef)
    (h10 : M 1 0 = conj (M 0 1)) : 2 * ‖M 0 1‖ ≤ (M 0 0).re + (M 1 1).re := by sorry
