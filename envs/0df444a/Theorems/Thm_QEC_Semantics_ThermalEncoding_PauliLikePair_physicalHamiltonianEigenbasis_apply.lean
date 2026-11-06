-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_physicalHamiltonianEigenbasis_apply
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.physicalHamiltonianEigenbasis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:54:05.435193+00:00
-- url     : https://prove2.me/theorems/679a4291-5815-495a-ae7f-e33af7656b91
-- title:
--   Pauli Like Pair: physical Hamiltonian Eigenbasis apply
-- statement:
--   The transported product basis is genuinely an eigenbasis of the physical
--   Hamiltonian; this connects the spectral Gibbs construction to `A`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1071-L1112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1071-L1112

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.ThermalEncoding.PauliLikePair
variable (P : PauliLikePair H)
variable [Nontrivial P.AuxiliarySpace]
attribute [local instance] QEC.Semantics.ThermalEncoding.PauliLikePair._p2m_local_instance_c824123c1a_1011
omit [Nontrivial P.AuxiliarySpace]

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.physicalHamiltonianEigenbasis_apply
    (A : Operator H) (hX : Commute A P.x) (hZ : Commute A P.z)
    (hA : A.IsSymmetric)
    (qi : Fin 2 × Fin (Module.finrank Complex P.AuxiliarySpace)) :
    A (P.physicalHamiltonianEigenbasis A hZ hA qi) =
      (P.physicalHamiltonianEnergies A hZ hA qi : Complex) •
        P.physicalHamiltonianEigenbasis A hZ hA qi := by sorry
