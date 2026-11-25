-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramSchmidtSelfImaginary_sum_mem_of
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.sum_mem_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:18.086984+00:00
-- url     : https://prove2.me/theorems/419cb77d-0b97-4655-8b04-c5a4d0c80c32
-- title:
--   Gram Schmidt Self Imaginary: sum mem of
-- statement:
--   The Gram Schmidt Self Imaginary construction uses the sum mem of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpSpanRight.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpSpanRight.lean#L66-L72

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

theorem ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.sum_mem_of {n : ℕ} (Y : Fin n → Fin r → ℂ) (S : Set (Fin n)) (w : Fin n → ℂ)
    (hw : ∀ j, j ∉ S → w j = 0) : ∑ j, w j • Y j ∈ Submodule.span ℂ (Y '' S) := by sorry
