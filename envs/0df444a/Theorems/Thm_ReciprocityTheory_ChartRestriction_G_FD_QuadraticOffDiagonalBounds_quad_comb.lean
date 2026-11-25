-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticOffDiagonalBounds_quad_comb
-- name    : ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds.quad_comb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:40.116437+00:00
-- url     : https://prove2.me/theorems/e88a564c-11c4-47d8-93fc-0db5a1a35803
-- title:
--   Quadratic Off Diagonal Bounds: quad comb
-- statement:
--   The Quadratic Off Diagonal Bounds construction uses the quad comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticOffDiagonalBounds.lean#L23-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticOffDiagonalBounds.lean#L23-L42

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

theorem ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds.quad_comb {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef) (α β : ℂ)
    (v w : Fin 2 → ℂ) :
    (∑ i, ∑ k, M i k * (α • v + β • w) i * conj ((α • v + β • w) k)).re ≤
      (‖α‖ ^ 2 + ‖β‖ ^ 2) * ((∑ i, ∑ k, M i k * v i * conj (v k)).re +
        (∑ i, ∑ k, M i k * w i * conj (w k)).re) := by sorry
