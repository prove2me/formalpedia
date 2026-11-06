-- Prove2me | Theorems.Thm_QEC_Semantics_protectedObservableStorageHorizon
-- name    : QEC.Semantics.protectedObservableStorageHorizon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:13:47.64038+00:00
-- url     : https://prove2.me/theorems/4dd73eda-3495-418b-91bf-d3473d38dacd
-- title:
--   Semantics: protected Observable Storage Horizon
-- statement:
--   The exact CLBT displacement estimate gives an encoded and decoded storage
--   horizon at every nonnegative target tolerance.  The final conjunct records the
--   zero-rate branch explicitly, so no division by a vanishing rate is used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/StorageHorizon.lean#L24-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/StorageHorizon.lean#L24-L133

import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Semantics_Dynamics_StorageHorizon
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics
variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]

theorem QEC.Semantics.protectedObservableStorageHorizon
    {a : Type} [Nontrivial K] [Fintype a]
    (logical : ThermalEncoding.PauliLikePair K)
    (hamiltonian : Operator K) (hhamiltonian : hamiltonian.IsSymmetric)
    (beta : ℝ) (J : a → Operator K) (P : Operator K)
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
        (∀ (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ)
            (_hdelta : 0 ≤ delta) (ht : 0 ≤ t),
          8 * t * lindbladDissipatorNorm J *
              clbtGibbsTailMass P
                (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) ≤
            delta →
          traceNorm
              (((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t
                    ht)
                  |>.mapDensity (Enc.mapDensity eta)).toOperator -
                (Enc.mapDensity eta).toOperator) ≤ delta ∧
          traceNorm
              ((Dec.mapDensity
                  ((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t
                      ht)
                    |>.mapDensity (Enc.mapDensity eta))).toOperator -
                eta.toOperator) ≤ delta) ∧
        (lindbladDissipatorNorm J *
              clbtGibbsTailMass P
                (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) = 0 →
          ∀ (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t),
            traceNorm
                (((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
                    |>.mapDensity (Enc.mapDensity eta)).toOperator -
                  (Enc.mapDensity eta).toOperator) = 0 ∧
            traceNorm
                ((Dec.mapDensity
                    ((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
                      |>.mapDensity (Enc.mapDensity eta))).toOperator -
                  eta.toOperator) = 0) := by sorry
