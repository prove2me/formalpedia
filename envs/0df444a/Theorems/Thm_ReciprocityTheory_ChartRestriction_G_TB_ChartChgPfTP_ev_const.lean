-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ev_const
-- name    : ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ev_const
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:26.405999+00:00
-- url     : https://prove2.me/theorems/e822dd12-7033-5996-ad2b-b3e7f604208e
-- title:
--   Chart Chg Pf TP: ev const
-- statement:
--   The Chart Chg Pf TP construction uses the ev const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L206-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L206-L212

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
variable {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ev_const {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ p q, constantCoeff (a p q) = 0) (f : PS k m d)
    (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 := by sorry
