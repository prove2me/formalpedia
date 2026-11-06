-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
-- name    : QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:21:03.957772+00:00
-- url     : https://prove2.me/theorems/d65e6eb0-9cd9-4909-81d0-3e2add30d8ca
-- title:
--   Finite Instrument: conditional Density to Operator
-- statement:
--   The Finite Instrument construction uses the conditional Density to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L184-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L184-L190

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

theorem QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator (I : FiniteInstrument κ Ω H K)
    (outcome : Ω) (rho : DensityOperator H)
    (hpos : 0 < I.bornWeight outcome rho) :
    (I.conditionalDensity outcome rho hpos).toOperator =
      ((I.bornWeight outcome rho : Complex)⁻¹) •
        I.branchOperator outcome rho.toOperator := by sorry

attribute [defeq] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
