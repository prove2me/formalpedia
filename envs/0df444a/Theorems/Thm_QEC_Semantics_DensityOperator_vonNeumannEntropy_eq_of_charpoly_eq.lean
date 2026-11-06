-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_of_charpoly_eq
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_of_charpoly_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:32:01.085966+00:00
-- url     : https://prove2.me/theorems/febcaf15-43dd-4fad-8c03-eb962435d6d5
-- title:
--   Density Operator: von Neumann Entropy eq of charpoly eq
-- statement:
--   Equality of finite characteristic-polynomial spectra implies equal entropy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L85-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L85-L91

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

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_of_charpoly_eq {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K)
    (hcharpoly : rho.toOperator.charpoly = sigma.toOperator.charpoly) :
    rho.vonNeumannEntropy = sigma.vonNeumannEntropy := by sorry
