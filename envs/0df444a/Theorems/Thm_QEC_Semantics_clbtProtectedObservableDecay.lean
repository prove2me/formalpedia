-- Prove2me | Theorems.Thm_QEC_Semantics_clbtProtectedObservableDecay
-- name    : QEC.Semantics.clbtProtectedObservableDecay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:29:42.738037+00:00
-- url     : https://prove2.me/theorems/780a4519-81e2-4308-9491-ecccf97ffe44
-- title:
--   Semantics: clbt Protected Observable Decay
-- statement:
--   Chesi--Loss--Bravyi--Terhal Theorem 1: protected Pauli-like observables give
--   TPCP thermal encoding and decoding maps with an exact left inverse and an
--   all-time factor-eight trace-norm decay bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ProtectedObservableDecay.lean#L623-L706
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ProtectedObservableDecay.lean#L623-L706

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

theorem QEC.Semantics.clbtProtectedObservableDecay
    {K ι : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    [Nontrivial K] [Fintype ι]
    (logical : ThermalEncoding.PauliLikePair K)
    (hamiltonian : Operator K) (hhamiltonian : hamiltonian.IsSymmetric)
    (beta : ℝ) (J : ι → Operator K) (P : Operator K)
    (hP : IsStarProjection P)
    (hPx : Commute P logical.x) (hPz : Commute P logical.z)
    (hHx : Commute hamiltonian logical.x)
    (hHz : Commute hamiltonian logical.z)
    (hPH : Commute P hamiltonian)
    (hprotectedX : JumpProtected J logical.x P)
    (hprotectedZ : JumpProtected J logical.z P)
    (hstationary : lindbladDissipator J
      (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta).toOperator = 0) :
    ∃ Enc : QuantumChannel Qubit.QubitSpace K,
      ∃ Dec : QuantumChannel K Qubit.QubitSpace,
        (∀ eta : DensityOperator Qubit.QubitSpace,
          Dec.mapDensity (Enc.mapDensity eta) = eta) ∧
        ∀ (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t),
          traceNorm
              (((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
                  |>.mapDensity (Enc.mapDensity eta)).toOperator -
                (Enc.mapDensity eta).toOperator) ≤
            8 * t * lindbladDissipatorNorm J *
              clbtGibbsTailMass P
                (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) := by sorry
