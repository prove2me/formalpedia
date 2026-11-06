-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_physicalGibbsState_eq_thermalReferenceState
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.physicalGibbsState_eq_thermalReferenceState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:24:06.347627+00:00
-- url     : https://prove2.me/theorems/5828f54b-460f-43f6-94c7-ace4183a68c8
-- title:
--   Pauli Like Pair: physical Gibbs State eq thermal Reference State
-- statement:
--   The Gibbs density of a Hamiltonian commuting with the derived Pauli pair
--   factors as the maximally mixed logical qubit tensor the auxiliary Gibbs
--   density.  Both the factorization and the auxiliary Hamiltonian are derived.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1161-L1188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1161-L1188

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

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.physicalGibbsState_eq_thermalReferenceState
    [Nontrivial P.AuxiliarySpace]
    (A : Operator H) (hZ : Commute A P.z)
    (hA : A.IsSymmetric) (beta : Real) :
    P.physicalGibbsState A hZ hA beta =
      P.thermalReferenceState (P.auxiliaryGibbsState A hZ hA beta) := by sorry
