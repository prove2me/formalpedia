-- Prove2me | Theorems.Thm_P2M_GlobalTheory_GaugeBaseChange_baseChange_zero__6485ee57f770
-- name    : P2M_GlobalTheory_GaugeBaseChange_baseChange_zero__6485ee57f770
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:01.887512+00:00
-- url     : https://prove2.me/theorems/d9df0663-b34d-487f-a89a-e372ba04e343
-- title:
--   P2 M Global Theory Gauge Base Change base Change zero  6485ee57f770: P2 M Global Theory Gauge Base Change base Change zero  6485ee57f770
-- statement:
--   The P2 M Global Theory Gauge Base Change base Change zero  6485ee57f770 construction uses the P2 M Global Theory Gauge Base Change base Change zero  6485ee57f770 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonGaugeNabValBaseChange.lean#L29-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonGaugeNabValBaseChange.lean#L29-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeNabValBaseChange
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.GaugeBaseChange
open GlobalTheory.QuadDeriv
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {d : ℕ}

theorem P2M_GlobalTheory_GaugeBaseChange_baseChange_zero__6485ee57f770 {n : ℕ} : mapP φ (0 : Pt k n d) = 0 := by sorry

alias «GlobalTheory».«GaugeBaseChange».«baseChange_zero₂» := P2M_GlobalTheory_GaugeBaseChange_baseChange_zero__6485ee57f770
