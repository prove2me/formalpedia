-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticOffDiagonalBounds_coord
-- name    : ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds.coord
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:48.153471+00:00
-- url     : https://prove2.me/theorems/8f17ce59-e6dc-4740-aa87-8da19ae8e01e
-- title:
--   Quadratic Off Diagonal Bounds: coord
-- statement:
--   The Quadratic Off Diagonal Bounds construction uses the coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticOffDiagonalBounds.lean#L81-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticOffDiagonalBounds.lean#L81-L126

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
variable {r : ℕ} {X : Data E r}

theorem ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds.coord {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (f1 f2 e : Fin r → ℂ) (a0 a1 : ℂ)
    (c : ℝ) (he : e = a0 • f1 + a1 • f2) (h1 : c * (X.Hf z τ f1 f1).re = 1)
    (h2 : X.Hf z τ e f1 = 0) (h3 : c * (X.Hf z τ e e).re = 1) :
    ∃ p q : ℂ, q * a0 + p = 0 ∧ q * a1 = 1 ∧ ‖p‖ ^ 2 + ‖q‖ ^ 2 = c * (X.Hf z τ f2 f2).re := by sorry
