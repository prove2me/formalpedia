-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_positive_bornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
-- name    : QEC.Semantics.FiniteInstrument.sum_positive_bornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:37:09.362325+00:00
-- url     : https://prove2.me/theorems/ce52f990-402e-4259-8eea-49cc81f0ee46
-- title:
--   Finite Instrument: sum positive born Weight smul conditional Density eq map Density to Operator
-- statement:
--   The positive observable branches, weighted by their Born probabilities,
--   reconstruct the unconditional complete-channel output. Zero-weight outcomes
--   are omitted only after proving that their raw branches vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L207-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L207-L265

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

theorem QEC.Semantics.FiniteInstrument.sum_positive_bornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
    (I : FiniteInstrument κ Ω H K) (hComplete : I.kraus.Complete)
    (rho : DensityOperator H) :
    (∑ outcome : {outcome : Ω // 0 < I.bornWeight outcome rho},
        (I.bornWeight outcome.1 rho : Complex) •
          (I.conditionalDensity outcome.1 rho outcome.2).toOperator) =
      ((I.kraus.toQuantumChannel hComplete).mapDensity rho).toOperator := by sorry
