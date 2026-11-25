-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_sub__879aecc3fdb2
-- name    : P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_sub__879aecc3fdb2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:15.203086+00:00
-- url     : https://prove2.me/theorems/3235da05-acf3-4db5-a85c-aee8e769bc59
-- title:
--   P2 M Global Theory Companion Theory Inert Doubling is Int sub  879aecc3fdb2: P2 M Global Theory Companion Theory Inert Doubling is Int sub  879aecc3fdb2
-- statement:
--   The P2 M Global Theory Companion Theory Inert Doubling is Int sub  879aecc3fdb2 construction uses the P2 M Global Theory Companion Theory Inert Doubling is Int sub  879aecc3fdb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L80-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CompletionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.Doubling GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDoubling
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_sub__879aecc3fdb2 {m p : Type} {A B : Matrix m p L} (h : IsInt A) (h' : IsInt B) : IsInt (A - B) := by sorry

alias «GlobalTheory».«CompanionTheory».«InertDoubling».«isInt_sub'» := P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_sub__879aecc3fdb2
