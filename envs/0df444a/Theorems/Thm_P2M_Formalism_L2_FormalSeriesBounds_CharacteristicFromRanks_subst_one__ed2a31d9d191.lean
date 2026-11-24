-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_subst_one__ed2a31d9d191
-- name    : P2M_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_subst_one__ed2a31d9d191
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:18.695639+00:00
-- url     : https://prove2.me/theorems/0b3c772f-51bc-4074-ab9c-b462f1ba351a
-- title:
--   P2 M Formalism L2 Formal Series Bounds Characteristic From Ranks subst one  ed2a31d9d191: P2 M Formalism L2 Formal Series Bounds Characteristic From Ranks subst one  ed2a31d9d191
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds Characteristic From Ranks subst one  ed2a31d9d191 construction uses the P2 M Formalism L2 Formal Series Bounds Characteristic From Ranks subst one  ed2a31d9d191 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L116-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L116-L118

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
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
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
variable {C : Type} [Field C]

theorem P2M_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_subst_one__ed2a31d9d191 {σ τ : Type} (a : σ → MvPowerSeries τ C) :
    MvPowerSeries.subst a (1 : MvPowerSeries σ C) = 1 := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«CharacteristicFromRanks».«subst_one'» := P2M_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_subst_one__ed2a31d9d191
