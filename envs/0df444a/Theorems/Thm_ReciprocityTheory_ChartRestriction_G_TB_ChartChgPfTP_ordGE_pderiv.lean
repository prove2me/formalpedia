-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ordGE_pderiv
-- name    : ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ordGE_pderiv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:46.365797+00:00
-- url     : https://prove2.me/theorems/d2a68f35-54a2-5b3b-af2c-a5d554ac35c0
-- title:
--   Chart Chg Pf TP: ord GE pderiv
-- statement:
--   The Chart Chg Pf TP construction uses the ord GE pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L39-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
variable {k : Type} [CommRing k]

theorem ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ordGE_pderiv {σ : Type} {r : ℕ} (i : σ) {g : MvPowerSeries σ k} (h : OrdGE (r + 1) g) :
    OrdGE r (pderiv k i g) := by sorry
