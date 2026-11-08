-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_fourDimensionalToric_linearEnergyBarrier_theta
-- name    : QEC.Coding.PeriodicCubical4.fourDimensionalToric_linearEnergyBarrier_theta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:45:15.717551+00:00
-- url     : https://prove2.me/theorems/4f8bb14e-1439-4b5b-bd96-3cf8a2166d86
-- title:
--   Periodic Cubical4: four Dimensional Toric linear Energy Barrier theta
-- statement:
--   Finite `Theta(L)` energy-barrier bounds for every nonzero primal and dual
--   coordinate-membrane sector of the periodic four-dimensional toric code.
--
--   Every single-plaquette Pauli path ending in any specified sector has BT
--   excess-energy height at least `L / 2`. Conversely, concatenating at most six
--   coordinate-framed basis sweeps gives an explicit path to every sector with
--   height at most `384 * L`. Each individual basis sweep retains the sharper
--   `64 * L` bound proved in #570.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QuantumMemory/FourDimensionalEnergyBarrier.lean#L37-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QuantumMemory/FourDimensionalEnergyBarrier.lean#L37-L62

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
import Definitions.Def_QEC_Results_QuantumMemory_FourDimensionalEnergyBarrier
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.fourDimensionalToric_linearEnergyBarrier_theta :
    (∀ (s : MembraneSector) (γ : PauliErrorPath (ι := Plaquette L)),
      HasPrimalSectorEndpoint γ s →
        L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ) ∧
    (∀ (s : MembraneSector) (γ : PauliErrorPath (ι := Plaquette L)),
      HasDualSectorEndpoint γ s →
        L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ) ∧
    (∀ s : MembraneSector,
      HasPrimalSectorEndpoint (primalSectorSweepPath (L := L) s) s ∧
        (toricHamiltonian (L := L)).pathHeight
          (primalSectorSweepPath (L := L) s) ≤ 384 * L) ∧
    (∀ s : MembraneSector,
      HasDualSectorEndpoint (dualSectorSweepPath (L := L) s) s ∧
        (toricHamiltonian (L := L)).pathHeight
          (dualSectorSweepPath (L := L) s) ≤ 384 * L) := by sorry
