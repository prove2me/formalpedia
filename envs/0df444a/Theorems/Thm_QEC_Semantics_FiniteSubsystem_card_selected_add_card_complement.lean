-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selected_add_card_complement
-- name    : QEC.Semantics.FiniteSubsystem.card_selected_add_card_complement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:42:52.82853+00:00
-- url     : https://prove2.me/theorems/deccff46-e6a4-4455-9d81-0e7753c28281
-- title:
--   Finite Subsystem: card selected add card complement
-- statement:
--   Selected and complement coordinate cardinalities partition the full coordinate count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L125-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L125-L129

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

theorem QEC.Semantics.FiniteSubsystem.card_selected_add_card_complement (S : FiniteSubsystem ι) :
    Fintype.card S.SelectedCoordinates + Fintype.card S.ComplementCoordinates =
      Fintype.card ι := by sorry
