-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_bt09_two_dimensional_constant_energy_barrier
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.bt09_two_dimensional_constant_energy_barrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:33:13.192671+00:00
-- url     : https://prove2.me/theorems/a0624c6c-f99a-42bf-932a-a8c551b15e8a
-- title:
--   Local Stabilizer Hamiltonian: bt09 two dimensional constant energy barrier
-- statement:
--   BT09 Theorem 2, in the selected-generator and single-qubit-walk conventions.
--
--   The disjunction is exactly the audited open/periodic boundary split.  The
--   explicit bound depends only on the common range upper bound and the recorded
--   qubit-participation bound, never on `L`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QuantumMemory/TwoDimensionalEnergyBarrier.lean#L33-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QuantumMemory/TwoDimensionalEnergyBarrier.lean#L33-L125

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Results_QuantumMemory_TwoDimensionalEnergyBarrier
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u
variable {κ : Type u} [Fintype κ]

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.bt09_two_dimensional_constant_energy_barrier
    {L r : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L) (hr : 2 ≤ r)
    (hBoundary :
      (StripGeometry.HasOpenIntervalGeneratorSupport H r ∧
        StripGeometry.HasOpenRowIntervalGeneratorSupport H r) ∨
      (StripGeometry.HasPeriodicIntervalGeneratorSupport H r ∧
        StripGeometry.HasPeriodicRowIntervalGeneratorSupport H r))
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    H.logicalEnergyBarrier ≤
      8 * r ^ 4 * H.participationBound := by sorry
