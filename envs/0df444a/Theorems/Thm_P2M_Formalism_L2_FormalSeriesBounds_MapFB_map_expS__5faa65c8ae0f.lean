-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_MapFB_map_expS__5faa65c8ae0f
-- name    : P2M_Formalism_L2_FormalSeriesBounds_MapFB_map_expS__5faa65c8ae0f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:34.430495+00:00
-- url     : https://prove2.me/theorems/e3d657a5-7554-41b5-a08a-d13ff4e735c0
-- title:
--   P2 M Formalism L2 Formal Series Bounds Map FB map exp S  5faa65c8ae0f: P2 M Formalism L2 Formal Series Bounds Map FB map exp S  5faa65c8ae0f
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds Map FB map exp S  5faa65c8ae0f construction uses the P2 M Formalism L2 Formal Series Bounds Map FB map exp S  5faa65c8ae0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNabMapSt.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNabMapSt.lean#L56-L59

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGaugeMapSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePNabMapSt
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.MapFB
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {K C : Type} [Field K] [Field C] (φ : K →+* C) {d : ℕ}

theorem P2M_Formalism_L2_FormalSeriesBounds_MapFB_map_expS__5faa65c8ae0f [Algebra ℚ K] [Algebra ℚ C] {n : ℕ} (f : PS K n d) (hf : constantCoeff f = 0) :
    MvPowerSeries.map φ (FB.expS K f) = FB.expS C (MvPowerSeries.map φ f) := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«MapFB».«map_expS'» := P2M_Formalism_L2_FormalSeriesBounds_MapFB_map_expS__5faa65c8ae0f
