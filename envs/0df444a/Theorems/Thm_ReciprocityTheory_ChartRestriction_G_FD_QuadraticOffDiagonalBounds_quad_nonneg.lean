-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticOffDiagonalBounds_quad_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds.quad_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:34.045562+00:00
-- url     : https://prove2.me/theorems/35af1619-9d82-4b11-8fd7-52fcf7c8bfd7
-- title:
--   Quadratic Off Diagonal Bounds: quad nonneg
-- statement:
--   The Quadratic Off Diagonal Bounds construction uses the quad nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticOffDiagonalBounds.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticOffDiagonalBounds.lean#L12-L21

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

theorem ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds.quad_nonneg {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef) (v : Fin 2 → ℂ) :
    0 ≤ (∑ i, ∑ k, M i k * v i * conj (v k)).re := by sorry
