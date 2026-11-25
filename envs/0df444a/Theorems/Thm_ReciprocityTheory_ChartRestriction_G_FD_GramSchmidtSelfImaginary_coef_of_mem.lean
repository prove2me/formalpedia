-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramSchmidtSelfImaginary_coef_of_mem
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.coef_of_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:37.083519+00:00
-- url     : https://prove2.me/theorems/7fc48135-ec34-525e-a039-4405047eebe7
-- title:
--   Gram Schmidt Self Imaginary: coef of mem
-- statement:
--   The Gram Schmidt Self Imaginary construction uses the coef of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpSpanRight.lean#L44-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpSpanRight.lean#L44-L64

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

theorem ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.coef_of_mem {n : ℕ} (Y : Fin n → Fin r → ℂ) (S : Set (Fin n)) {v : Fin r → ℂ}
    (hv : v ∈ Submodule.span ℂ (Y '' S)) :
    ∃ w : Fin n → ℂ, (∀ j, j ∉ S → w j = 0) ∧ v = ∑ j, w j • Y j := by sorry
