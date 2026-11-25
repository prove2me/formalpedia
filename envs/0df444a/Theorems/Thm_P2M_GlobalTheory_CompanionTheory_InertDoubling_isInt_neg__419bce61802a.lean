-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_neg__419bce61802a
-- name    : P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_neg__419bce61802a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:03:46.388832+00:00
-- url     : https://prove2.me/theorems/4c48f47e-156a-4dd9-ad95-49485cc0f516
-- title:
--   P2 M Global Theory Companion Theory Inert Doubling is Int neg  419bce61802a: P2 M Global Theory Companion Theory Inert Doubling is Int neg  419bce61802a
-- statement:
--   The P2 M Global Theory Companion Theory Inert Doubling is Int neg  419bce61802a construction uses the P2 M Global Theory Companion Theory Inert Doubling is Int neg  419bce61802a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L78-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L78-L78

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

theorem P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_neg__419bce61802a {m p : Type} {A : Matrix m p L} (h : IsInt A) : IsInt (-A) := by sorry

alias «GlobalTheory».«CompanionTheory».«InertDoubling».«isInt_neg'» := P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_neg__419bce61802a
