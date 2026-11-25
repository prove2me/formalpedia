-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientLattice_span_gen
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.span_gen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:30.621105+00:00
-- url     : https://prove2.me/theorems/f2979b84-6726-4898-8193-ee11d738a84e
-- title:
--   Fourier Coefficient Lattice: span gen
-- statement:
--   The Fourier Coefficient Lattice construction uses the span gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientLattice.lean#L354-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientLattice.lean#L354-L368

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.span_gen (T : (X.Ψ → ℝ) →ₗ[ℝ] (X.Ψ → Fin 2 → Fin 2 → ℝ))
    (hT : ∀ a : E, cc a = a → IsIntegral ℤ a →
      T (fun τ => (τ.1 a).re) ∈ Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)))
    (p : X.Ψ → ℝ) : T p ∈ Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)) := by sorry
