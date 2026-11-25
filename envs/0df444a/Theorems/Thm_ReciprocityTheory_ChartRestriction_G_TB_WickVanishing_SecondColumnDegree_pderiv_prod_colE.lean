-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_pderiv_prod_colE
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.pderiv_prod_colE
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:42:18.586394+00:00
-- url     : https://prove2.me/theorems/69d7d50b-acce-4812-aeed-8561af302203
-- title:
--   Second Column Degree: pderiv prod col E
-- statement:
--   The Second Column Degree construction uses the pderiv prod col E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnDegree.lean#L161-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnDegree.lean#L161-L169

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
variable {ι : Type} [Fintype ι] {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.pderiv_prod_colE (b : Fin n) (s : Finset (Fin n)) (hb : b ∉ s) (Q : Fin n → MvPolynomial ι k)
    (l : ι) : pderiv (l, b) (∏ b' ∈ s, colE b' (Q b')) = 0 := by sorry
