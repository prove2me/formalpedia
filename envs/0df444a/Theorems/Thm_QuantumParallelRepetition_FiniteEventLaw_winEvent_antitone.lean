-- Prove2me | Theorems.Thm_QuantumParallelRepetition_FiniteEventLaw_winEvent_antitone
-- name    : QuantumParallelRepetition.FiniteEventLaw.winEvent_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/b47d8a5a-a532-4942-b429-cf21b372dc71
-- title:
--   QuantumParallelRepetition.FiniteEventLaw.winEvent_antitone
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators
open QuantumParallelRepetition.FiniteEventLaw
variable {Ω ι : Type*} [Fintype Ω]

theorem QuantumParallelRepetition.FiniteEventLaw.winEvent_antitone [Fintype ι]
    (wins : ι → Ω → Bool) {D E : Finset ι} (h : D ⊆ E) :
    winEvent wins E ⊆ winEvent wins D := by sorry
