-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_sum_star_inner_mul_inner_eq_inner
-- name    : QEC.Semantics.QuditSubsystem.sum_star_inner_mul_inner_eq_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:21.001149+00:00
-- url     : https://prove2.me/theorems/3fe4b9f0-9b75-4952-afda-d55d3dcf7cf1
-- title:
--   Qudit Subsystem: sum star inner mul inner eq inner
-- statement:
--   The Qudit Subsystem construction uses the sum star inner mul inner eq inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L326-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L326-L342

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

theorem QEC.Semantics.QuditSubsystem.sum_star_inner_mul_inner_eq_inner {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H) (x y : H) :
    (∑ a : κ, star (inner Complex (b a) x) * inner Complex (b a) y) =
      inner Complex x y := by sorry
