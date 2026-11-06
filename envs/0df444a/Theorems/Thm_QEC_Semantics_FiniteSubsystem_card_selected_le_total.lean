-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selected_le_total
-- name    : QEC.Semantics.FiniteSubsystem.card_selected_le_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:42:40.089226+00:00
-- url     : https://prove2.me/theorems/b2b61c3f-3d40-433a-97b0-ae4198b4a459
-- title:
--   Finite Subsystem: card selected le total
-- statement:
--   A selected finite coordinate set has cardinality at most the full coordinate type.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L132-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L132-L134

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

theorem QEC.Semantics.FiniteSubsystem.card_selected_le_total (S : FiniteSubsystem ι) :
    Fintype.card S.SelectedCoordinates ≤ Fintype.card ι := by sorry
