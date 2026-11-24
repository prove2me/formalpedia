-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_span_eq_of_mat
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.span_eq_of_mat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:44:41.046232+00:00
-- url     : https://prove2.me/theorems/ce4403ac-0560-4d19-8e54-755a1be61ba6
-- title:
--   Positive Span Matrices: span eq of mat
-- statement:
--   The Positive Span Matrices construction uses the span eq of mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PositiveSpanMatrices.lean#L42-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PositiveSpanMatrices.lean#L42-L63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.span_eq_of_mat {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (f g : Fin n → V)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0) (h : ∀ b, g b = ∑ b', A b' b • f b') :
    Submodule.span ℂ (Set.range g) = Submodule.span ℂ (Set.range f) := by sorry
