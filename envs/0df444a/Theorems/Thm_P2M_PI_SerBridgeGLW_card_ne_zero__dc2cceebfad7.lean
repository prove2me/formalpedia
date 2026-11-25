-- Prove2me | Theorems.Thm_P2M_PI_SerBridgeGLW_card_ne_zero__dc2cceebfad7
-- name    : P2M_PI_SerBridgeGLW_card_ne_zero__dc2cceebfad7
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:58:18.193129+00:00
-- url     : https://prove2.me/theorems/b7408516-133d-4c7e-bfe1-31a071ab29bc
-- title:
--   P2 M PI Ser Bridge GLW card ne zero  dc2cceebfad7: P2 M PI Ser Bridge GLW card ne zero  dc2cceebfad7
-- statement:
--   The P2 M PI Ser Bridge GLW card ne zero  dc2cceebfad7 construction uses the P2 M PI Ser Bridge GLW card ne zero  dc2cceebfad7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/CharacterEqOfRepIso.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/CharacterEqOfRepIso.lean#L11-L12

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open PI PI.SerBridgeGLW
variable {G : Type} [Group G] [Fintype G]

theorem P2M_PI_SerBridgeGLW_card_ne_zero__dc2cceebfad7 : (Nat.card G : ℂ) ≠ 0 := by sorry

alias «PI».«SerBridgeGLW».«card_ne_zero'» := P2M_PI_SerBridgeGLW_card_ne_zero__dc2cceebfad7
