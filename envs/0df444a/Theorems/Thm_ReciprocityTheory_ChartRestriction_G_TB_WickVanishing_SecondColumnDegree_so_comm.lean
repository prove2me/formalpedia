-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_comm
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.so_comm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:42:56.118547+00:00
-- url     : https://prove2.me/theorems/691b6a82-eb12-50fe-8656-00ce73b1a154
-- title:
--   Second Column Degree: so comm
-- statement:
--   The Second Column Degree construction uses the so comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnDegree.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnDegree.lean#L60-L68

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.so_comm (c1 c2 : σ → σ → k) (P : MvPolynomial σ k) :
    secondOrder k c1 (secondOrder k c2 P) = secondOrder k c2 (secondOrder k c1 P) := by sorry
