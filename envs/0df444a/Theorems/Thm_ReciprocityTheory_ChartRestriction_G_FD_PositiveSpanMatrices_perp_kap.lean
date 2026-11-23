-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_perp_kap
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.perp_kap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:50.7027+00:00
-- url     : https://prove2.me/theorems/d62026a1-cc8d-4356-b80f-e136c22d2ac1
-- title:
--   Positive Span Matrices: perp kap
-- statement:
--   The Positive Span Matrices construction uses the perp kap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PositiveSpanMatrices.lean#L173-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PositiveSpanMatrices.lean#L173-L181

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

theorem ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.perp_kap {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (w : Fin r → ℂ) (hw : w ∈ Spos X x τ)
    (a : Fin (r - X.p0)) : hermC τ.1 X.Gm w (col (mat x τ) (kap X.p0_le a)) = 0 := by sorry
