-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_basisMatrixSpectrum
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_basisMatrixSpectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:16:41.683591+00:00
-- url     : https://prove2.me/theorems/d3a9d18d-a2ee-4a7d-8f2a-8a75575782fd
-- title:
--   Density Operator: von Neumann Entropy eq basis Matrix Spectrum
-- statement:
--   The entropy is independent of the coordinate basis used for its matrix spectrum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L94-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L94-L101

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_basisMatrixSpectrum
    (rho : DensityOperator H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    rho.vonNeumannEntropy =
      (((rho.toOperator.toMatrix b.toBasis b.toBasis).charpoly.roots.map Complex.re).map
        entropyTerm).sum := by sorry
