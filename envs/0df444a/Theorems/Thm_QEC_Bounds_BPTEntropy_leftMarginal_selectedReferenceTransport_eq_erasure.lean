-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_leftMarginal_selectedReferenceTransport_eq_erasure
-- name    : QEC.Bounds.BPTEntropy.leftMarginal_selectedReferenceTransport_eq_erasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:19.816196+00:00
-- url     : https://prove2.me/theorems/cf09eb71-ad93-40b7-b5b5-b47f28e7ce5f
-- title:
--   BPTEntropy: left Marginal selected Reference Transport eq erasure
-- statement:
--   The complementary marginal of the selected/reference transport is precisely
--   the concrete erasure channel applied after tracing out the untouched reference.
--   This is the heterogeneous `global register -> complement` bridge used by the
--   BPT correctable-region entropy identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L142-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L142-L196

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
set_option maxHeartbeats 800000

theorem QEC.Bounds.BPTEntropy.leftMarginal_selectedReferenceTransport_eq_erasure
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S : QuditSubsystem q) (Ref : Type u)
    [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref] [FiniteQuantumSystem Ref]
    (omega : DensityOperator (CompositeSystem (Qudit.QuditRegister q) Ref)) :
    leftMarginal ((S.selectedReferenceTransport Ref).conjDensity omega) =
      S.erasureChannelFromRegister.mapDensity (rightMarginal omega) := by sorry
