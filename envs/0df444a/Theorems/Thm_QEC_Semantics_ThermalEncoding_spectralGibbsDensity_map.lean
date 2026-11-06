-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_spectralGibbsDensity_map
-- name    : QEC.Semantics.ThermalEncoding.spectralGibbsDensity_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:23:29.275431+00:00
-- url     : https://prove2.me/theorems/aa67e236-86c5-430a-90bd-01ddfaee6dc0
-- title:
--   Thermal Encoding: spectral Gibbs Density map
-- statement:
--   Spectral Gibbs densities commute with a unitary change of eigenbasis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L311-L336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L311-L336

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

theorem QEC.Semantics.ThermalEncoding.spectralGibbsDensity_map {ι K : Type}
    [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K)
    (b : OrthonormalBasis ι Complex H) (energy : ι → Real) (beta : Real) :
    spectralGibbsDensity (b.map U.toLinearIsometryEquiv) energy beta =
      U.conjDensity (spectralGibbsDensity b energy beta) := by sorry
