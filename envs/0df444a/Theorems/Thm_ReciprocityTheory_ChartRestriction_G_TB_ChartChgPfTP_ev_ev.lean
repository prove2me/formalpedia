-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ev_ev
-- name    : ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ev_ev
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:21.639406+00:00
-- url     : https://prove2.me/theorems/1f5cb2f2-fd21-54ff-b27a-67dc6b6c791d
-- title:
--   Chart Chg Pf TP: ev ev
-- statement:
--   The Chart Chg Pf TP construction uses the ev ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L193-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L193-L198

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

theorem ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ev_ev {m n r : ℕ} (a : Fin m → Pt k n d) (b : Fin n → Pt k r d) (ha : ∀ p q, constantCoeff (a p q) = 0)
    (hb : ∀ p q, constantCoeff (b p q) = 0) (f : PS k m d) :
    ev b (ev a f) = ev (fun p q => ev b (a p q)) f := by sorry
