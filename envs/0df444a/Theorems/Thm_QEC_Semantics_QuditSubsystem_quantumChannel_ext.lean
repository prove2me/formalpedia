-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_quantumChannel_ext
-- name    : QEC.Semantics.QuditSubsystem.quantumChannel_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:48:32.513233+00:00
-- url     : https://prove2.me/theorems/e51677c9-9c22-4bc5-adcb-6e55af35e6ac
-- title:
--   Qudit Subsystem: quantum Channel ext
-- statement:
--   The Qudit Subsystem construction uses the quantum Channel ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L25-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L25-L32

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.QuditSubsystem
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.quantumChannel_ext {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi Psi : QuantumChannel H K) (h : Phi.toLinearMap = Psi.toLinearMap) : Phi = Psi := by sorry
