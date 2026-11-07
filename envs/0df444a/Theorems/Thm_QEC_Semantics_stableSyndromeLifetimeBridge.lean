-- Prove2me | Theorems.Thm_QEC_Semantics_stableSyndromeLifetimeBridge
-- name    : QEC.Semantics.stableSyndromeLifetimeBridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:33:35.15769+00:00
-- url     : https://prove2.me/theorems/29b7fb6c-14f7-4c43-949f-f3a00bc4fdbc
-- title:
--   Semantics: stable Syndrome Lifetime Bridge
-- statement:
--   The public M11 bridge.  The Pauli-like pair, protected good sector, jump
--   protectedness, and Gibbs bad-sector identity are all derived from the concrete
--   decoder and selected elementary Pauli errors.  The only dynamical premise is
--   the source-required stationarity of the resulting Gibbs state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QuantumMemory/StableSyndromeStorage.lean#L30-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QuantumMemory/StableSyndromeStorage.lean#L30-L155

import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Semantics_Dynamics_StorageHorizon
import Definitions.Def_QEC_Results_QuantumMemory_StableSyndromeStorage
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedX_adjoint
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedX_anticommute_dressedZ
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedX_square
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedZ_adjoint
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedZ_commute_hamiltonian
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedZ_square
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_operator_adjoint_eq_self
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedX_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedX_square
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedZ_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedZ_square


set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics
open QEC.Coding.StabilizerCode
open QEC.Coding.PauliSymplectic
variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]

theorem QEC.Semantics.stableSyndromeLifetimeBridge
    {iota kappa a : Type}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa] [Fintype a]
    (H : LocalStabilizerHamiltonian (ι := iota) (κ := kappa))
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary iota))
    (jumpError : a → Binary iota)
    (hjumpError : ∀ b, jumpError b ∈ elementaryErrors)
    (beta : ℝ) :
    let logical : ThermalEncoding.PauliLikePair (Qubit.QubitRegister iota) :=
      { x := D.dressedX
        z := D.dressedZ
        x_symmetric :=
          (LinearMap.isSymmetric_iff_isSelfAdjoint D.dressedX).mpr
            D.dressedX_adjoint
        z_symmetric :=
          (LinearMap.isSymmetric_iff_isSelfAdjoint D.dressedZ).mpr
            D.dressedZ_adjoint
        x_sq := D.dressedX_square
        z_sq := D.dressedZ_square
        anticommute := D.dressedX_anticommute_dressedZ }
    let hhamiltonian : H.operator.IsSymmetric :=
      (LinearMap.isSymmetric_iff_isSelfAdjoint H.operator).mpr
        H.operator_adjoint_eq_self
    let J : a → Operator (Qubit.QubitRegister iota) :=
      fun b ↦ toHermitianQubitOperator (jumpError b)
    let auxiliaryNontrivial : Nontrivial logical.AuxiliarySpace :=
      ThermalEncoding.PauliLikePair.auxiliarySpaceNontrivial logical
    let rhoBeta := @ThermalEncoding.PauliLikePair.physicalGibbsState
      (Qubit.QubitRegister iota) inferInstance inferInstance inferInstance logical
      auxiliaryNontrivial H.operator D.dressedZ_commute_hamiltonian.symm
      hhamiltonian beta
    lindbladDissipator J rhoBeta.toOperator = 0 →
      logical.x.IsSymmetric ∧
      logical.z.IsSymmetric ∧
      logical.x * logical.x = 1 ∧
      logical.z * logical.z = 1 ∧
      logical.x * logical.z = -(logical.z * logical.x) ∧
      Commute logical.x H.operator ∧
      Commute logical.z H.operator ∧
      DecoderDressedLogical.GoodSyndromeProtectedObservable D elementaryErrors ∧
      JumpProtected J D.dressedX (D.goodSyndromeProjector elementaryErrors) ∧
      JumpProtected J D.dressedZ (D.goodSyndromeProjector elementaryErrors) ∧
      ∃ Enc : QuantumChannel Qubit.QubitSpace (Qubit.QubitRegister iota),
        ∃ Dec : QuantumChannel (Qubit.QubitRegister iota) Qubit.QubitSpace,
          (∀ eta : DensityOperator Qubit.QubitSpace,
            Dec.mapDensity (Enc.mapDensity eta) = eta) ∧
          (∀ (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ)
              (_hdelta : 0 ≤ delta) (ht : 0 ≤ t),
            8 * t * lindbladDissipatorNorm J *
                Complex.re (D.badSyndromeGibbsWeight elementaryErrors rhoBeta) ≤
              delta →
            traceNorm
                (((finiteLindbladEvolutionChannel H.operator J hhamiltonian t
                      ht)
                    |>.mapDensity (Enc.mapDensity eta)).toOperator -
                  (Enc.mapDensity eta).toOperator) ≤ delta ∧
            traceNorm
                ((Dec.mapDensity
                    ((finiteLindbladEvolutionChannel H.operator J hhamiltonian t
                        ht)
                      |>.mapDensity (Enc.mapDensity eta))).toOperator -
                  eta.toOperator) ≤ delta) ∧
          (lindbladDissipatorNorm J *
                Complex.re (D.badSyndromeGibbsWeight elementaryErrors rhoBeta) = 0 →
            ∀ (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t),
              traceNorm
                  (((finiteLindbladEvolutionChannel H.operator J hhamiltonian t ht)
                      |>.mapDensity (Enc.mapDensity eta)).toOperator -
                    (Enc.mapDensity eta).toOperator) = 0 ∧
              traceNorm
                  ((Dec.mapDensity
                      ((finiteLindbladEvolutionChannel H.operator J hhamiltonian t ht)
                        |>.mapDensity (Enc.mapDensity eta))).toOperator -
                    eta.toOperator) = 0) := by sorry
