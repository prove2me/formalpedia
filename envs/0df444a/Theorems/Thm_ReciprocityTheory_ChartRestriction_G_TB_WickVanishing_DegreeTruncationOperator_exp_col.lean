-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_exp_col
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator.exp_col
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:57:22.319587+00:00
-- url     : https://prove2.me/theorems/03c78c0e-2355-5abb-b6f5-e443f259e2da
-- title:
--   Degree Truncation Operator: exp col
-- statement:
--   The Degree Truncation Operator construction uses the exp col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnOperator.lean#L190-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnOperator.lean#L190-L199

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
open SecondColumnDegree
variable {k : Type} [CommRing k] [Algebra ℚ k]
variable {ι : Type} [Fintype ι] {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator.exp_col (c : ι → ι → k) (t : k) (N : ℕ) (Q : Fin n → MvPolynomial ι k) (b0 : Fin n)
    (hdeg : (prodQ Q).totalDegree ≤ N) :
    IsNilpotent.exp (opA (cB c b0) t N) (prodQ Q) = prodQ (Function.update Q b0 (E1 c t N (Q b0))) := by sorry
