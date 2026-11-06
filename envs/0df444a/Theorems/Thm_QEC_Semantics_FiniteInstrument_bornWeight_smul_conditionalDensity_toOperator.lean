-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_smul_conditionalDensity_toOperator
-- name    : QEC.Semantics.FiniteInstrument.bornWeight_smul_conditionalDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:18:42.948361+00:00
-- url     : https://prove2.me/theorems/ee5666ce-8e44-4b8e-af9b-e81b10c6022f
-- title:
--   Finite Instrument: born Weight smul conditional Density to Operator
-- statement:
--   Weighting a positive-mass conditional density recovers its raw branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L193-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L193-L200

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Instruments_Core
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
attribute [local instance] QEC.Semantics.FiniteInstrument._p2m_local_instance_a5f1a79248_39

theorem QEC.Semantics.FiniteInstrument.bornWeight_smul_conditionalDensity_toOperator
    (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (rho : DensityOperator H) (hpos : 0 < I.bornWeight outcome rho) :
    (I.bornWeight outcome rho : Complex) •
        (I.conditionalDensity outcome rho hpos).toOperator =
      I.branchOperator outcome rho.toOperator := by sorry
