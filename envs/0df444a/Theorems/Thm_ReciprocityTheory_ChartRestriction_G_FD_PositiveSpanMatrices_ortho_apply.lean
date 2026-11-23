-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_ortho_apply
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.ortho_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:24.0895+00:00
-- url     : https://prove2.me/theorems/37e46d67-7971-4d78-8d82-ad15b5ffe71e
-- title:
--   Positive Span Matrices: ortho apply
-- statement:
--   The Positive Span Matrices construction uses the ortho apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PositiveSpanMatrices.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PositiveSpanMatrices.lean#L90-L93

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.ortho_apply {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (c d : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) c) (col (mat x τ) d) = if c = d then ((sgn X.p0 c : ℝ) : ℂ) else 0 := by sorry
