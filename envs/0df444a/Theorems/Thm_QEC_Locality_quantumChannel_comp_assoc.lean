-- Prove2me | Theorems.Thm_QEC_Locality_quantumChannel_comp_assoc
-- name    : QEC.Locality.quantumChannel_comp_assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:40:51.078437+00:00
-- url     : https://prove2.me/theorems/b131a927-a8a9-4320-91e1-26a33b9e9e23
-- title:
--   Locality: quantum Channel comp assoc
-- statement:
--   The Locality construction uses the quantum Channel comp assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L1014-L1023
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L1014-L1023

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.quantumChannel_comp_assoc {H K L M : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    [NormedAddCommGroup M] [InnerProductSpace Complex M] [FiniteQuantumSystem M]
    (Phi : QuantumChannel H K) (Psi : QuantumChannel K L) (Omega : QuantumChannel L M) :
    QuantumChannel.comp Omega (QuantumChannel.comp Psi Phi) =
      QuantumChannel.comp (QuantumChannel.comp Omega Psi) Phi := by sorry
