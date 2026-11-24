-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertCoset_mem_intL__232cca9d9091
-- name    : P2M_GlobalTheory_CompanionTheory_InertCoset_mem_intL__232cca9d9091
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:54:48.799126+00:00
-- url     : https://prove2.me/theorems/fa9126d8-61bd-482d-b822-ccc272d9ad0d
-- title:
--   P2 M Global Theory Companion Theory Inert Coset mem int L  232cca9d9091: P2 M Global Theory Companion Theory Inert Coset mem int L  232cca9d9091
-- statement:
--   The P2 M Global Theory Companion Theory Inert Coset mem int L  232cca9d9091 construction uses the P2 M Global Theory Companion Theory Inert Coset mem int L  232cca9d9091 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L133-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L133-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem P2M_GlobalTheory_CompanionTheory_InertCoset_mem_intL__232cca9d9091 {x : L} : x ∈ intL L ↔ Valued.v x ≤ 1 := by sorry

alias «GlobalTheory».«CompanionTheory».«InertCoset».«mem_intL'» := P2M_GlobalTheory_CompanionTheory_InertCoset_mem_intL__232cca9d9091
