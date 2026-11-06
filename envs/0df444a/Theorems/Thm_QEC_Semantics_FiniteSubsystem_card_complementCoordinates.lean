-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
-- name    : QEC.Semantics.FiniteSubsystem.card_complementCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:07:13.034013+00:00
-- url     : https://prove2.me/theorems/e198cf9b-1ae2-4ab3-a147-5e2fe649aa98
-- title:
--   Finite Subsystem: card complement Coordinates
-- statement:
--   The Finite Subsystem construction uses the card complement Coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L119-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L119-L122

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.card_complementCoordinates (S : FiniteSubsystem ι) :
    Fintype.card S.ComplementCoordinates = S.selectedᶜ.card := by sorry
