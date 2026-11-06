-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
-- name    : QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:06:39.465906+00:00
-- url     : https://prove2.me/theorems/9a13175c-db19-460a-b363-31a31179ecf9
-- title:
--   Finite Subsystem: card selected Coordinates
-- statement:
--   The Finite Subsystem construction uses the card selected Coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L114-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L114-L116

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

theorem QEC.Semantics.FiniteSubsystem.card_selectedCoordinates (S : FiniteSubsystem ι) :
    Fintype.card S.SelectedCoordinates = S.selected.card := by sorry
