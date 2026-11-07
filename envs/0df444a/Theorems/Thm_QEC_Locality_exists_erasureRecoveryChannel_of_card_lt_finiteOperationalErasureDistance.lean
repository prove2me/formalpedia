-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecoveryChannel_of_card_lt_finiteOperationalErasureDistance
-- name    : QEC.Locality.exists_erasureRecoveryChannel_of_card_lt_finiteOperationalErasureDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:13:03.177214+00:00
-- url     : https://prove2.me/theorems/42a14daa-f93e-4620-8d6c-fba4402118d4
-- title:
--   Locality: exists erasure Recovery Channel of card lt finite Operational Erasure Distance
-- statement:
--   A subsystem smaller than the local convention has a concrete CPTP recovery
--   channel from its finite-subsystem erasure channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/OperationalErasureDistance.lean#L91-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/OperationalErasureDistance.lean#L91-L102

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Locality_CorrectableRegions_OperationalErasureDistance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.exists_erasureRecoveryChannel_of_card_lt_finiteOperationalErasureDistance
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι))
    (S : Semantics.FiniteSubsystem ι) {d : Nat}
    (hDistance : d = finiteOperationalErasureDistance C)
    (hCard : S.selected.card < d) :
    ∃ recovery : Semantics.QuantumChannel S.complementSystem
        (Semantics.Qubit.QubitRegister ι),
      Semantics.Correctable (Semantics.Qubit.QubitRegister ι) S.complementSystem C
        S.erasureChannelFromRegister recovery := by sorry
