-- Prove2me | Theorems.Thm_QEC_QLDPC_eventually_chainComplexBoundaryIncidence_boundedLocality_of_uniform_boundary_bounds
-- name    : QEC.QLDPC.eventually_chainComplexBoundaryIncidence_boundedLocality_of_uniform_boundary_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:39:48.064079+00:00
-- url     : https://prove2.me/theorems/841e6664-fd3c-4e58-87d6-2e955d92f96e
-- title:
--   QLDPC: eventually chain Complex Boundary Incidence bounded Locality of uniform boundary bounds
-- statement:
--   Uniform boundary row/check and column/variable bounds for a Nat-indexed binary
--   chain-complex family give the same bounded-locality witness for every valid
--   family member after `start`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L739-L767
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L739-L767

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.eventually_chainComplexBoundaryIncidence_boundedLocality_of_uniform_boundary_bounds
    {ι κ lambda : Nat → Type u}
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    [∀ n, Fintype (κ n)] [∀ n, Fintype (lambda n)]
    (validIndex : Nat → Prop) (start : Nat)
    (K : ∀ n, Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) (κ n))
      (Coding.Word (ZMod 2) (ι n))
      (Coding.Word (ZMod 2) (lambda n)))
    {w variableDegree : Nat}
    (hrow1 : ∀ n, start ≤ n → validIndex n → ∀ k,
      Coding.HammingWeight
        (Coding.wordLinearMapTranspose (K n).boundary1
          (Coding.canonicalBasisWord (F := ZMod 2) k)) ≤ w)
    (hrow2 : ∀ n, start ≤ n → validIndex n → ∀ l,
      Coding.HammingWeight ((K n).boundary2
        (Coding.canonicalBasisWord (F := ZMod 2) l)) ≤ w)
    (hcol : ∀ n, start ≤ n → validIndex n → ∀ q,
      ((chainComplexBoundaryIncidence (K n)).variableSupport q).card ≤ variableDegree) :
    ∀ n, start ≤ n → validIndex n →
      Coding.BoundedLocality
        (chainComplexBoundaryIncidence (K n)).localityProfile
        (max w variableDegree) := by sorry
