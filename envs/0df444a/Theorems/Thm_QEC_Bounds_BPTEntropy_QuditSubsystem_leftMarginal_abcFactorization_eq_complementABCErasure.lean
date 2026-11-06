-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_leftMarginal_abcFactorization_eq_complementABCErasure
-- name    : QEC.Bounds.BPTEntropy.QuditSubsystem.leftMarginal_abcFactorization_eq_complementABCErasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:59.496862+00:00
-- url     : https://prove2.me/theorems/a22253d7-2c81-4367-a668-bef4ced31061
-- title:
--   Qudit Subsystem: left Marginal abc Factorization eq complement ABCErasure
-- statement:
--   The Qudit Subsystem construction uses the left Marginal abc Factorization eq complement ABCErasure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1169-L1221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1169-L1221

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

theorem QEC.Bounds.BPTEntropy.QuditSubsystem.leftMarginal_abcFactorization_eq_complementABCErasure
    (S T : QuditSubsystem q) (hST : Disjoint S.selected T.selected)
    (rho : DensityOperator (Qudit.QuditRegister q)) :
    leftMarginal ((abcFactorization S T hST).conjDensity rho) =
      (complementABCFactorization S T hST).conjDensity
        (S.erasureChannelFromRegister.mapDensity rho) := by sorry
