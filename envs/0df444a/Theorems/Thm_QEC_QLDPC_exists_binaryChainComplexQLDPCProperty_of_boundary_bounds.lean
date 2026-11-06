-- Prove2me | Theorems.Thm_QEC_QLDPC_exists_binaryChainComplexQLDPCProperty_of_boundary_bounds
-- name    : QEC.QLDPC.exists_binaryChainComplexQLDPCProperty_of_boundary_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:24:18.310837+00:00
-- url     : https://prove2.me/theorems/f62f3e64-85d2-41f3-ba8f-c41ee6458a91
-- title:
--   QLDPC: exists binary Chain Complex QLDPCProperty of boundary bounds
-- statement:
--   Explicit finite-coordinate chain-complex boundary row/column bounds give an
--   honest per-code binary qLDPC property for the associated chain-complex CSS code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L695-L732
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L695-L732

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.exists_binaryChainComplexQLDPCProperty_of_boundary_bounds
    {ι κ lambda : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda))
    (parameters : Coding.CodeParameters (ZMod 2) ι)
    {w variableDegree : Nat}
    (hrow1 : ∀ k, Coding.HammingWeight
      (Coding.wordLinearMapTranspose K.boundary1
        (Coding.canonicalBasisWord (F := ZMod 2) k)) ≤ w)
    (hrow2 : ∀ l, Coding.HammingWeight
      (K.boundary2 (Coding.canonicalBasisWord (F := ZMod 2) l)) ≤ w)
    (hcol : ∀ q, ((chainComplexBoundaryIncidence K).variableSupport q).card ≤
      variableDegree) :
    ∃ P : Coding.QLDPCProperty (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)
      (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda),
      P.chainCode = K.binaryChainComplexCode ∧
      P.parameters = parameters ∧
      P.locality = (chainComplexBoundaryIncidence K).localityProfile ∧
      P.localityBound = max w variableDegree := by sorry
