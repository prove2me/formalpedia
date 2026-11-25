-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_of_mem_lex
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_of_mem_lex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:36.988963+00:00
-- url     : https://prove2.me/theorems/c88d70f5-8f3b-412a-8ace-83cbbbb80f42
-- title:
--   Arakelov Geometry: is Multi Homog of mem lex
-- statement:
--   The Arakelov Geometry construction uses the is Multi Homog of mem lex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsPrimeFiltrationOfIsMultiHomogIdeal.lean#L50-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsPrimeFiltrationOfIsMultiHomogIdeal.lean#L50-L59

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_of_mem_lex (e : K ≃ Fin n) {f : MRing ι} {m : Lex (Fin n → ℕ)}
    (h : f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) m) :
    IsMultiHomog f (fun k => ofLex m (e k)) := by sorry
