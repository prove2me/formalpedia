-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_iter_deg_le
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.so_iter_deg_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:42:41.207749+00:00
-- url     : https://prove2.me/theorems/c872a356-aa0f-560d-b0e5-12373809f509
-- title:
--   Second Column Degree: so iter deg le
-- statement:
--   The Second Column Degree construction uses the so iter deg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnDegree.lean#L125-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnDegree.lean#L125-L132

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.so_iter_deg_le (c : σ → σ → k) :
    ∀ (i : ℕ) (Q : MvPolynomial σ k), ((secondOrder k c)^[i] Q).totalDegree ≤ Q.totalDegree
  := by sorry
