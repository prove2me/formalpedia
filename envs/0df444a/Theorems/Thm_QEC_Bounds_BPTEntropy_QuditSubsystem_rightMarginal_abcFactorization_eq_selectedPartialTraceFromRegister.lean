-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_rightMarginal_abcFactorization_eq_selectedPartialTraceFromRegister
-- name    : QEC.Bounds.BPTEntropy.QuditSubsystem.rightMarginal_abcFactorization_eq_selectedPartialTraceFromRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:28:00.18769+00:00
-- url     : https://prove2.me/theorems/a3514efb-ef2d-4f88-8a72-4eb15dadf9e1
-- title:
--   Qudit Subsystem: right Marginal abc Factorization eq selected Partial Trace From Register
-- statement:
--   The Qudit Subsystem construction uses the right Marginal abc Factorization eq selected Partial Trace From Register property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1106-L1163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1106-L1163

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u
open QEC.Bounds.BPTEntropy.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι -> Nat}
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem QEC.Bounds.BPTEntropy.QuditSubsystem.rightMarginal_abcFactorization_eq_selectedPartialTraceFromRegister
    (S T : QuditSubsystem q) (hST : Disjoint S.selected T.selected)
    (rho : DensityOperator (Qudit.QuditRegister q)) :
    rightMarginal ((abcFactorization S T hST).conjDensity rho) =
      S.selectedPartialTraceFromRegister.mapDensity rho := by sorry
