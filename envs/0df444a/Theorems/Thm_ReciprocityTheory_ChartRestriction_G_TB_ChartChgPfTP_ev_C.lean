-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ev_C
-- name    : ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ev_C
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:33.701804+00:00
-- url     : https://prove2.me/theorems/956e6083-1e93-43ae-85a5-3ef86d21f01a
-- title:
--   Chart Chg Pf TP: ev C
-- statement:
--   The Chart Chg Pf TP construction uses the ev C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L242-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L242-L251

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

theorem ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ev_C {m n : ℕ} {a : Fin m → Pt k n d} (ha : ∀ p q, constantCoeff (a p q) = 0) (c : k) :
    ev a (C c : PS k m d) = C c := by sorry
