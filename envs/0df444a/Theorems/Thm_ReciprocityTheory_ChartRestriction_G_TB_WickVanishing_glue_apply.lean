-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_glue_apply
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.glue_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:03:40.0819+00:00
-- url     : https://prove2.me/theorems/57653689-0209-53f6-9fbf-68d098c086c8
-- title:
--   Wick Vanishing: glue apply
-- statement:
--   The Wick Vanishing construction uses the glue apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TruncatedExpSecondEqFull.lean#L69-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TruncatedExpSecondEqFull.lean#L69-L79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TruncatedExpSecondEqFull
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
open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open SecondColumnDegree DegreeTruncationOperator
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.glue_apply (g : Fin n → (ι →₀ ℕ)) (l : ι) (b : Fin n) : glue g (l, b) = g b l := by sorry
