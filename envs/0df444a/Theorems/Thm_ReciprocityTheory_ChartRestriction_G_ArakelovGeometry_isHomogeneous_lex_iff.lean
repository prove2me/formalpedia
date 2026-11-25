-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isHomogeneous_lex_iff
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isHomogeneous_lex_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:41.113833+00:00
-- url     : https://prove2.me/theorems/5ce72ee3-3716-4d8c-b015-1a94f23ec496
-- title:
--   Arakelov Geometry: is Homogeneous lex iff
-- statement:
--   The Arakelov Geometry construction uses the is Homogeneous lex iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsPrimeFiltrationOfIsMultiHomogIdeal.lean#L66-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsPrimeFiltrationOfIsMultiHomogIdeal.lean#L66-L79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
attribute [local instance 2000] lexDecEq
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isHomogeneous_lex_iff (e : K ≃ Fin n) (J : Ideal (MRing ι)) :
    J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) ↔ IsMultiHomogIdeal J := by sorry
