-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_col_mul__2f207898769f
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_col_mul__2f207898769f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:19.802465+00:00
-- url     : https://prove2.me/theorems/3eeae468-707e-4d23-bb3c-c371d992ecad
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Lower Block Matrices col mul  2f207898769f: P2 M Reciprocity Theory Chart Restriction G FD Lower Block Matrices col mul  2f207898769f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Lower Block Matrices col mul  2f207898769f construction uses the P2 M Reciprocity Theory Chart Restriction G FD Lower Block Matrices col mul  2f207898769f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LowerBlockMatrices.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LowerBlockMatrices.lean#L23-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BlockIdentityExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowerBlockMatrices
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

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_col_mul__2f207898769f (A B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : _root_.ReciprocityTheory.ChartRestriction.G.FD.col (A * B) a = A *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.col B a := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«LowerBlockMatrices».«col_mul'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_col_mul__2f207898769f
