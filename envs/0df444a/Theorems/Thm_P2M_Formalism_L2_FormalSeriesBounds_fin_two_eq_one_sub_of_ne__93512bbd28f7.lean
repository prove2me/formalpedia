-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_fin_two_eq_one_sub_of_ne__93512bbd28f7
-- name    : P2M_Formalism_L2_FormalSeriesBounds_fin_two_eq_one_sub_of_ne__93512bbd28f7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:11.418854+00:00
-- url     : https://prove2.me/theorems/8e33e64d-b59f-48c1-8fbc-bc205c00b068
-- title:
--   P2 M Formalism L2 Formal Series Bounds fin two eq one sub of ne  93512bbd28f7: P2 M Formalism L2 Formal Series Bounds fin two eq one sub of ne  93512bbd28f7
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds fin two eq one sub of ne  93512bbd28f7 construction uses the P2 M Formalism L2 Formal Series Bounds fin two eq one sub of ne  93512bbd28f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L122-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L122-L122

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
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
variable {dd : ℕ}

theorem P2M_Formalism_L2_FormalSeriesBounds_fin_two_eq_one_sub_of_ne__93512bbd28f7 : ∀ g g' : Fin 2, g' ≠ g → g' = 1 - g := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«fin_two_eq_one_sub_of_ne'» := P2M_Formalism_L2_FormalSeriesBounds_fin_two_eq_one_sub_of_ne__93512bbd28f7
