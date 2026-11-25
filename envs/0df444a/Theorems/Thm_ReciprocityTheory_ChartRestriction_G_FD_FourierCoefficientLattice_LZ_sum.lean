-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientLattice_LZ_sum
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.LZ_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:14:53.860776+00:00
-- url     : https://prove2.me/theorems/e7988b23-7a3e-563b-bff3-0284857d010c
-- title:
--   Fourier Coefficient Lattice: LZ sum
-- statement:
--   The Fourier Coefficient Lattice construction uses the LZ sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientLattice.lean#L121-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientLattice.lean#L121-L129

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.LZ_sum {N : ℕ} {ω : Fin N → X.Ψ → Fin 2 → Fin 2 → ℂ} (hω : ∀ j, ω j ∈ X.LZ g)
    (n : Fin N → ℤ) : ∑ j, (n j : ℂ) • ω j ∈ X.LZ g := by sorry
