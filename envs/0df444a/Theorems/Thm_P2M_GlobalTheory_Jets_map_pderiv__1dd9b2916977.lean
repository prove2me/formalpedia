-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Jets_map_pderiv__1dd9b2916977
-- name    : P2M_GlobalTheory_Jets_map_pderiv__1dd9b2916977
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:51:21.631812+00:00
-- url     : https://prove2.me/theorems/a9caf821-bcfa-42ce-9875-3dbf95f2588c
-- title:
--   P2 M Global Theory Jets map pderiv  1dd9b2916977: P2 M Global Theory Jets map pderiv  1dd9b2916977
-- statement:
--   The P2 M Global Theory Jets map pderiv  1dd9b2916977 construction uses the P2 M Global Theory Jets map pderiv  1dd9b2916977 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HasSubstAddSqZero.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HasSubstAddSqZero.lean#L78-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.Jets

theorem P2M_GlobalTheory_Jets_map_pderiv__1dd9b2916977 {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (i : σ)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv R i f) = pderiv S i (MvPowerSeries.map φ f) := by sorry

alias «GlobalTheory».«Jets».«map_pderiv'» := P2M_GlobalTheory_Jets_map_pderiv__1dd9b2916977
