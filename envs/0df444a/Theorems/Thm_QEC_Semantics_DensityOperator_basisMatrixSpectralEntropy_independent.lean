-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_basisMatrixSpectralEntropy_independent
-- name    : QEC.Semantics.DensityOperator.basisMatrixSpectralEntropy_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:45:09.613196+00:00
-- url     : https://prove2.me/theorems/0d885431-97f7-46db-a145-a63e60e43dc4
-- title:
--   Density Operator: basis Matrix Spectral Entropy independent
-- statement:
--   Two orthonormal coordinate bases give the same finite spectral entropy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L104-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L104-L112

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

theorem QEC.Semantics.DensityOperator.basisMatrixSpectralEntropy_independent
    (rho : DensityOperator H)
    (b c : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    (((rho.toOperator.toMatrix b.toBasis b.toBasis).charpoly.roots.map Complex.re).map
        entropyTerm).sum =
      (((rho.toOperator.toMatrix c.toBasis c.toBasis).charpoly.roots.map Complex.re).map
        entropyTerm).sum := by sorry
