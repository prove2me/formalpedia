-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_buildCorrectionHistory_eq_of_recursion
-- name    : QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_eq_of_recursion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:28:51.95483+00:00
-- url     : https://prove2.me/theorems/b402fa6d-8949-4d86-ad05-95309abb5826
-- title:
--   Multiscale Decoder: build Correction History eq of recursion
-- statement:
--   The actual history agrees with any finite recursion having exactly its
--   base constructor and selected-step equation. This exposes uniqueness without
--   exporting the private recursive implementation or changing the algorithm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1576-L1614
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1576-L1614

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_eq_of_recursion
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (F : ∀ (n : Nat) (hn : n ≤ depth),
      D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩ → CorrectionHistory D)
    (hzero : ∀ hn sigma, F 0 hn sigma = [.base {
      input := sigma, correction := B.decode sigma,
      relation := (B.rightInverse sigma).symm }])
    (hsucc : ∀ (n : Nat) (hn : n+1 ≤ depth)
      (sigma : D.family.Syndrome ⟨n+1,Nat.lt_succ_of_le hn⟩),
      F (n+1) hn sigma =
        .step ⟨n,by omega⟩ (S.step ⟨n,by omega⟩ sigma) ::
          F n (by omega) (S.step ⟨n,by omega⟩ sigma).coarse)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    buildCorrectionHistory D S B sigma = F depth (Nat.le_refl _) sigma := by sorry
