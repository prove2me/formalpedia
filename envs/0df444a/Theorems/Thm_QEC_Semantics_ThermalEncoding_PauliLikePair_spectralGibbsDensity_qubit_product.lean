-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_spectralGibbsDensity_qubit_product
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.spectralGibbsDensity_qubit_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:23:52.515199+00:00
-- url     : https://prove2.me/theorems/917f9444-a9fc-45ec-aadf-bff5c86f293a
-- title:
--   Pauli Like Pair: spectral Gibbs Density qubit product
-- statement:
--   A duplicated qubit spectrum produces the maximally mixed qubit tensor its Gibbs state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L934-L996
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L934-L996

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.ThermalEncoding.PauliLikePair
variable (P : PauliLikePair H)

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.spectralGibbsDensity_qubit_product {ι : Type}
    [Fintype ι] [Nonempty ι]
    (b : OrthonormalBasis ι Complex P.AuxiliarySpace)
    (energy : ι → Real) (beta : Real) :
    spectralGibbsDensity
        ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct b)
        (fun qi : Fin 2 × ι => energy qi.2) beta =
      DensityOperator.tensorDensity maximallyMixedQubit
        (spectralGibbsDensity b energy beta) := by sorry
