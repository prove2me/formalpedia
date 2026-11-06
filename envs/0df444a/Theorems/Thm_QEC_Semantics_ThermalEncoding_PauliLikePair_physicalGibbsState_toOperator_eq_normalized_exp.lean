-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_physicalGibbsState_toOperator_eq_normalized_exp
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.physicalGibbsState_toOperator_eq_normalized_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:29:35.526247+00:00
-- url     : https://prove2.me/theorems/3cd23ec0-b8b7-41eb-804d-c2f9fd43054f
-- title:
--   Pauli Like Pair: physical Gibbs State to Operator eq normalized exp
-- statement:
--   The spectral Gibbs density constructed from the Pauli factorization is the
--   normalized operator exponential of the physical Hamiltonian.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ProtectedObservableDecay.lean#L293-L343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ProtectedObservableDecay.lean#L293-L343

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

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.physicalGibbsState_toOperator_eq_normalized_exp
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    [Nontrivial logical.AuxiliarySpace]
    (hamiltonian : Operator K)
    (hX : Commute hamiltonian logical.x)
    (hZ : Commute hamiltonian logical.z)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (beta : ℝ) :
    (logical.physicalGibbsState hamiltonian hZ hhamiltonian beta).toOperator =
      ((ThermalEncoding.gibbsPartitionFunction beta
        (logical.physicalHamiltonianEnergies hamiltonian hZ hhamiltonian) : ℂ)⁻¹) •
        (NormedSpace.exp
          ((-beta : ℂ) • LinearMap.toContinuousLinearMap hamiltonian)).toLinearMap := by sorry
