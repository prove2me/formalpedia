-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_commute_physicalGibbsState
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.commute_physicalGibbsState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:29:42.83631+00:00
-- url     : https://prove2.me/theorems/3be47806-fe97-49de-9d4f-267fb4107645
-- title:
--   Pauli Like Pair: commute physical Gibbs State
-- statement:
--   Every symmetric Hamiltonian commutant also commutes with its Gibbs density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ProtectedObservableDecay.lean#L346-L378
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ProtectedObservableDecay.lean#L346-L378

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped ComplexOrder
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
attribute [local instance] QEC.Semantics.clbtFiniteQuantumSystemComplete

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.commute_physicalGibbsState
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    [Nontrivial logical.AuxiliarySpace]
    (hamiltonian A : Operator K)
    (hX : Commute hamiltonian logical.x)
    (hZ : Commute hamiltonian logical.z)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (hA : Commute A hamiltonian)
    (beta : ℝ) :
    Commute A
      (logical.physicalGibbsState hamiltonian hZ hhamiltonian beta).toOperator := by sorry
