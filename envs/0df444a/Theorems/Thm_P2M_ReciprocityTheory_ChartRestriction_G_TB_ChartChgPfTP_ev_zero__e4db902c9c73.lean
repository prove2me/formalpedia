-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ev_zero__e4db902c9c73
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ev_zero__e4db902c9c73
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:26.651687+00:00
-- url     : https://prove2.me/theorems/8a88a2ff-4c7d-5857-9671-ba3bc8ca2122
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB Chart Chg Pf TP ev zero  e4db902c9c73: P2 M Reciprocity Theory Chart Restriction G TB Chart Chg Pf TP ev zero  e4db902c9c73
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB Chart Chg Pf TP ev zero  e4db902c9c73 construction uses the P2 M Reciprocity Theory Chart Restriction G TB Chart Chg Pf TP ev zero  e4db902c9c73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L253-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L253-L261

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ev_zero__e4db902c9c73 {m n : ℕ} {a : Fin m → Pt k n d} (ha : ∀ p q, constantCoeff (a p q) = 0) :
    ev a (0 : PS k m d) = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«ChartChgPfTP».«ev_zero'» := P2M_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ev_zero__e4db902c9c73
