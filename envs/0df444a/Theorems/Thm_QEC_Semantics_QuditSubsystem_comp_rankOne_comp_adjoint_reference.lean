-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_comp_rankOne_comp_adjoint_reference
-- name    : QEC.Semantics.QuditSubsystem.comp_rankOne_comp_adjoint_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:22.389505+00:00
-- url     : https://prove2.me/theorems/63980b89-362e-4b92-8dcb-cb7f9984228f
-- title:
--   Qudit Subsystem: comp rank One comp adjoint reference
-- statement:
--   The Qudit Subsystem construction uses the comp rank One comp adjoint reference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L315-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L315-L323

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

theorem QEC.Semantics.QuditSubsystem.comp_rankOne_comp_adjoint_reference {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (L : H →ₗ[Complex] K) (x y : H) :
    L.comp ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp (LinearMap.adjoint L)) =
      (InnerProductSpace.rankOne Complex (L x) (L y)).toLinearMap := by sorry
