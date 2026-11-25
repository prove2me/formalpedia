-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientLattice_span_fixed_integral_real_parts
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.span_fixed_integral_real_parts
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:50.740806+00:00
-- url     : https://prove2.me/theorems/52cbdbe1-0347-42a8-ba36-93fd0a565389
-- title:
--   Fourier Coefficient Lattice: span fixed integral real parts
-- statement:
--   The Fourier Coefficient Lattice construction uses the span fixed integral real parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientLattice.lean#L248-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientLattice.lean#L248-L352

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)

theorem ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.span_fixed_integral_real_parts : Submodule.span ℝ {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
    p = fun τ => (τ.1 a).re} = ⊤ := by sorry
