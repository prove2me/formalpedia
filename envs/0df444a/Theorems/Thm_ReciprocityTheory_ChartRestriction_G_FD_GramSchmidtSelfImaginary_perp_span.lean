-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramSchmidtSelfImaginary_perp_span
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.perp_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:01.984462+00:00
-- url     : https://prove2.me/theorems/11ca142b-01f4-472b-b872-3175d11ffcd2
-- title:
--   Gram Schmidt Self Imaginary: perp span
-- statement:
--   The Gram Schmidt Self Imaginary construction uses the perp span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpSpanRight.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpSpanRight.lean#L20-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

theorem ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.perp_span {s : Set (Fin r → ℂ)} {v : Fin r → ℂ} (h : ∀ y ∈ s, hermC τ G y v = 0) :
    ∀ y ∈ Submodule.span ℂ s, hermC τ G y v = 0 := by sorry
