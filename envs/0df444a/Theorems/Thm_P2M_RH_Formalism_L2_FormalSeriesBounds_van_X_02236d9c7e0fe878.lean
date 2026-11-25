-- Prove2me | Theorems.Thm_P2M_RH_Formalism_L2_FormalSeriesBounds_van_X_02236d9c7e0fe878
-- name    : P2M_RH_Formalism_L2_FormalSeriesBounds_van_X_02236d9c7e0fe878
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:07.499137+00:00
-- url     : https://prove2.me/theorems/e2bf39ad-0f5d-52fa-8d00-ba0dfd3efdaf
-- title:
--   P2 M RH Formalism L2 Formal Series Bounds van X 02236d9c7e0fe878: P2 M RH Formalism L2 Formal Series Bounds van X 02236d9c7e0fe878
-- statement:
--   The P2 M RH Formalism L2 Formal Series Bounds van X 02236d9c7e0fe878 construction uses the P2 M RH Formalism L2 Formal Series Bounds van X 02236d9c7e0fe878 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePAxesSelfSt.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePAxesSelfSt.lean#L21-L27

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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

theorem P2M_RH_Formalism_L2_FormalSeriesBounds_van_X_02236d9c7e0fe878 {τ : Type} {T : Set τ} {q : τ} (hq : q ∈ T) : Van T (X q : MvPowerSeries τ C) := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«van_X» := P2M_RH_Formalism_L2_FormalSeriesBounds_van_X_02236d9c7e0fe878
