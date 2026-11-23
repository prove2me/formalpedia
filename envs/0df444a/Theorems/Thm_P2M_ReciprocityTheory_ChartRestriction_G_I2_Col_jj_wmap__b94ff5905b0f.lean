-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_Col_jj_wmap__b94ff5905b0f
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_I2_Col_jj_wmap__b94ff5905b0f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:58.482036+00:00
-- url     : https://prove2.me/theorems/0f34a517-2df4-4f77-bf9b-84ce53be9e55
-- title:
--   P2 M Reciprocity Theory Chart Restriction G I2 Col jj wmap  b94ff5905b0f: P2 M Reciprocity Theory Chart Restriction G I2 Col jj wmap  b94ff5905b0f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G I2 Col jj wmap  b94ff5905b0f construction uses the P2 M Reciprocity Theory Chart Restriction G I2 Col jj wmap  b94ff5905b0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L255-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L255-L256

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {ι : Type} [Fintype ι]
variable (K : Submodule ℝ (EuclideanSpace ℂ ι))
variable {K}
variable (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
include hK

theorem P2M_ReciprocityTheory_ChartRestriction_G_I2_Col_jj_wmap__b94ff5905b0f (v : EuclideanSpace ℂ ι) : jj K (wmap K v) = p2 K v := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«I2».«Col».«jj_wmap'» := P2M_ReciprocityTheory_ChartRestriction_G_I2_Col_jj_wmap__b94ff5905b0f
