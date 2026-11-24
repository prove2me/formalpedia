-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_mulVec_eq_sum_col
-- name    : ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.mulVec_eq_sum_col
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:22.688855+00:00
-- url     : https://prove2.me/theorems/8d618165-fd2b-4958-9ea3-51cd9adad54a
-- title:
--   Lower Block Matrices: mul Vec eq sum col
-- statement:
--   The Lower Block Matrices construction uses the mul Vec eq sum col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LowerBlockMatrices.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LowerBlockMatrices.lean#L27-L30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BlockIdentityExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowerBlockMatrices
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mulVec_eq_sum_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.mulVec_eq_sum_col (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) : M *ᵥ w = ∑ c, w c • col M c := by sorry
