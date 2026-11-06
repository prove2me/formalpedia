-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_exists_finiteKrausFamily_representation
-- name    : QEC.Semantics.QuantumChannel.exists_finiteKrausFamily_representation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:19:26.009747+00:00
-- url     : https://prove2.me/theorems/634aa5c4-23cf-45ae-af30-faa8db9890fe
-- title:
--   Quantum Channel: exists finite Kraus Family representation
-- statement:
--   Every project quantum channel admits a complete finite Kraus representation
--   whose induced operator-space map is the channel map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L216-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L216-L227

import Definitions.Def_QEC_Semantics_Channels_Choi
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
open QEC.Semantics.QuantumChannel

theorem QEC.Semantics.QuantumChannel.exists_finiteKrausFamily_representation (Φ : QuantumChannel H K) :
    ∃ (m : Nat), ∃ R : FiniteKrausFamily (Fin m) H K,
      R.Complete ∧ R.inducedMap = Φ.toLinearMap := by sorry
