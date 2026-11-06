-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_rightMarginal_bacOfAbcFactorization_eq_selectedPartialTraceFromRegister
-- name    : QEC.Bounds.BPTEntropy.QuditSubsystem.rightMarginal_bacOfAbcFactorization_eq_selectedPartialTraceFromRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:28:08.268583+00:00
-- url     : https://prove2.me/theorems/1243b135-5c5f-490c-bffe-89f61b2759d1
-- title:
--   Qudit Subsystem: right Marginal bac Of Abc Factorization eq selected Partial Trace From Register
-- statement:
--   The Qudit Subsystem construction uses the right Marginal bac Of Abc Factorization eq selected Partial Trace From Register property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1314-L1374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1314-L1374

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

theorem QEC.Bounds.BPTEntropy.QuditSubsystem.rightMarginal_bacOfAbcFactorization_eq_selectedPartialTraceFromRegister
    (S T : QuditSubsystem q) (hST : Disjoint S.selected T.selected)
    (rho : DensityOperator (Qudit.QuditRegister q)) :
    rightMarginal
      ((abcToBac S.selectedSystem T.selectedSystem (unionSubsystem S T).complementSystem).conjDensity
        ((abcFactorization S T hST).conjDensity rho)) =
      T.selectedPartialTraceFromRegister.mapDensity rho := by sorry
