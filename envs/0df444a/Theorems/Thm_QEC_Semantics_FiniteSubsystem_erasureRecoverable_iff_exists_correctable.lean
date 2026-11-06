-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_erasureRecoverable_iff_exists_correctable
-- name    : QEC.Semantics.FiniteSubsystem.erasureRecoverable_iff_exists_correctable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:43:46.539397+00:00
-- url     : https://prove2.me/theorems/7cae4629-8ffe-4b7a-b101-fb507c04a656
-- title:
--   Finite Subsystem: erasure Recoverable iff exists correctable
-- statement:
--   Existential erasure recoverability stays in the M2 channel/correctability vocabulary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L368-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L368-L373

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

theorem QEC.Semantics.FiniteSubsystem.erasureRecoverable_iff_exists_correctable (S : FiniteSubsystem ι)
    (C : QuantumCode S.factorizedSystem) :
    S.ErasureRecoverable C ↔
      ∃ recovery : QuantumChannel S.complementSystem S.factorizedSystem,
        Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery := by sorry
