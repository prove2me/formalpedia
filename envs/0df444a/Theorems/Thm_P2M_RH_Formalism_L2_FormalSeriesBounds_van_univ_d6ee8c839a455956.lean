-- Prove2me | Theorems.Thm_P2M_RH_Formalism_L2_FormalSeriesBounds_van_univ_d6ee8c839a455956
-- name    : P2M_RH_Formalism_L2_FormalSeriesBounds_van_univ_d6ee8c839a455956
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:47:16.923803+00:00
-- url     : https://prove2.me/theorems/2092a54d-6dfd-5315-91a7-d9b3e292910a
-- title:
--   P2 M RH Formalism L2 Formal Series Bounds van univ d6ee8c839a455956: P2 M RH Formalism L2 Formal Series Bounds van univ d6ee8c839a455956
-- statement:
--   The P2 M RH Formalism L2 Formal Series Bounds van univ d6ee8c839a455956 construction uses the P2 M RH Formalism L2 Formal Series Bounds van univ d6ee8c839a455956 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePAxesSelfSt.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePAxesSelfSt.lean#L29-L37

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]

theorem P2M_RH_Formalism_L2_FormalSeriesBounds_van_univ_d6ee8c839a455956 {τ : Type} {f : MvPowerSeries τ C} (hf : constantCoeff f = 0) : Van Set.univ f := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«van_univ» := P2M_RH_Formalism_L2_FormalSeriesBounds_van_univ_d6ee8c839a455956
