-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramSchmidtSelfImaginary_hC_self_im
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.hC_self_im
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:21.408093+00:00
-- url     : https://prove2.me/theorems/d8a27727-6453-4d71-85b2-04118af89e67
-- title:
--   Gram Schmidt Self Imaginary: h C self im
-- statement:
--   The Gram Schmidt Self Imaginary construction uses the h C self im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpSpanRight.lean#L77-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpSpanRight.lean#L77-L92

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
variable (hG : ∀ a b, cc (G a b) = G b a)
include hG

theorem ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.hC_self_im (v : Fin r → ℂ) : (hermC τ G v v).im = 0 := by sorry
