-- Prove2me | Theorems.Thm_QEC_QLDPC_chainComplexCSSFamily_isLDPC_of_uniform_row_bounds
-- name    : QEC.QLDPC.chainComplexCSSFamily_isLDPC_of_uniform_row_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:40:24.393062+00:00
-- url     : https://prove2.me/theorems/9f0c239a-4083-434a-969a-2a36082aaa9a
-- title:
--   QLDPC: chain Complex CSSFamily is LDPC of uniform row bounds
-- statement:
--   Uniform boundary-row weights and middle-coordinate incidence degrees make a
--   family of source-valid chain-complex CSS stabilizer codes LDPC.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/SourceValidity.lean#L274-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/SourceValidity.lean#L274-L307

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
open scoped Classical
universe u w

theorem QEC.QLDPC.chainComplexCSSFamily_isLDPC_of_uniform_row_bounds
    {A : Type u} {ι κ lambda : A → Type w}
    [∀ a, Fintype (ι a)]
    [∀ a, Fintype (κ a)] [∀ a, Fintype (lambda a)]
    (K : ∀ a, Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) (κ a))
      (Coding.Word (ZMod 2) (ι a))
      (Coding.Word (ZMod 2) (lambda a)))
    {w : Nat}
    (hrowX : ∀ a k, Coding.HammingWeight
      (Coding.wordLinearMapTranspose (K a).boundary1
        (Pi.single k (1 : ZMod 2))) ≤ w)
    (hrowZ : ∀ a l, Coding.HammingWeight
      ((K a).boundary2 (Pi.single l (1 : ZMod 2))) ≤ w)
    (hdegree : ∀ a q,
      ((chainComplexBoundaryIncidence (K a)).variableSupport q).card ≤ w) :
    IsLDPCStabilizerFamily
      (fun a => (K a).binaryCSSSourceValidStabilizer) := by sorry
