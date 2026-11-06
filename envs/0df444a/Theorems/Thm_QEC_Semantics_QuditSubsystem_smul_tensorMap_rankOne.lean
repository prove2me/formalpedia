-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_smul_tensorMap_rankOne
-- name    : QEC.Semantics.QuditSubsystem.smul_tensorMap_rankOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:25.384971+00:00
-- url     : https://prove2.me/theorems/e9a07fa7-e3f5-491a-9141-f890bb503efc
-- title:
--   Qudit Subsystem: smul tensor Map rank One
-- statement:
--   The Qudit Subsystem construction uses the smul tensor Map rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L345-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L345-L353

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

theorem QEC.Semantics.QuditSubsystem.smul_tensorMap_rankOne {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (c : Complex) (x y : H) (u v : K) :
    c • (InnerProductSpace.rankOne Complex (x ⊗ₜ[Complex] u)
      (y ⊗ₜ[Complex] v)).toLinearMap =
      TensorProduct.map (c • (InnerProductSpace.rankOne Complex x y).toLinearMap)
        (InnerProductSpace.rankOne Complex u v).toLinearMap := by sorry
