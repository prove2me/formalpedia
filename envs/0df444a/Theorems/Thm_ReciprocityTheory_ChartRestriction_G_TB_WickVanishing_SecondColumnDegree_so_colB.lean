-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_colB
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.so_colB
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:44:01.38148+00:00
-- url     : https://prove2.me/theorems/6e4697e0-949c-5f85-ab47-b5972707ba7a
-- title:
--   Second Column Degree: so col B
-- statement:
--   The Second Column Degree construction uses the so col B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnDegree.lean#L171-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnDegree.lean#L171-L202

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.so_colB (c : ι → ι → k) (b : Fin n) (Q : MvPolynomial ι k) (R : MvPolynomial (ι × Fin n) k)
    (hR : ∀ l : ι, pderiv (l, b) R = 0) :
    secondOrder k (cB c b) (colE b Q * R) = colE b (secondOrder k c Q) * R := by sorry
