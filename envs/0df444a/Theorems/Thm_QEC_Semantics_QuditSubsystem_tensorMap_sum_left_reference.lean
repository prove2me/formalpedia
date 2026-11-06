-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_tensorMap_sum_left_reference
-- name    : QEC.Semantics.QuditSubsystem.tensorMap_sum_left_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:41.880278+00:00
-- url     : https://prove2.me/theorems/50173735-0e12-4e71-b43d-f03ee9a055af
-- title:
--   Qudit Subsystem: tensor Map sum left reference
-- statement:
--   The Qudit Subsystem construction uses the tensor Map sum left reference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1257-L1267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1257-L1267

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.tensorMap_sum_left_reference {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {κ : Type v} [Fintype κ] (f : κ → Operator H) (A : Operator K) :
    TensorProduct.map (∑ i, f i) A = ∑ i, TensorProduct.map (f i) A := by sorry
