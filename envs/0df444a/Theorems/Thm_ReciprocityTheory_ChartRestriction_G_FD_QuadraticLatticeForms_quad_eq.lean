-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_quad_eq
-- name    : ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.quad_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:26.50113+00:00
-- url     : https://prove2.me/theorems/18e512dc-f769-4c17-996a-3d8e2d4d0bca
-- title:
--   Quadratic Lattice Forms: quad eq
-- statement:
--   The Quadratic Lattice Forms construction uses the quad eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticLatticeForms.lean#L155-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticLatticeForms.lean#L155-L166

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_DetToMatrixSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
open Matrix NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.quad_eq (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (g : Basis ι ℤ X.Λ) (x : ι → ℝ) :
    x ⬝ᵥ (Am X y g *ᵥ x) = ip X (Ly X y (∑ i, x i • X.embV (g i : Fin r → E)))
      (Ly X y (∑ i, x i • X.embV (g i : Fin r → E))) := by sorry
