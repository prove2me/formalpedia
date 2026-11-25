-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_eq_zero_of_le_one
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.so_eq_zero_of_le_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:42:03.079175+00:00
-- url     : https://prove2.me/theorems/dfcbea31-90b4-4bd9-ac70-b7abf46de168
-- title:
--   Second Column Degree: so eq zero of le one
-- statement:
--   The Second Column Degree construction uses the so eq zero of le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnDegree.lean#L106-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnDegree.lean#L106-L111

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
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
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
variable {k : Type} [CommRing k]
variable {σ : Type} [Fintype σ]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.so_eq_zero_of_le_one (c : σ → σ → k) (Q : MvPolynomial σ k) (h : Q.totalDegree ≤ 1) :
    secondOrder k c Q = 0 := by sorry
