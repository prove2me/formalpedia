-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DetInv_PsiPhi_phiInv_frobenius__8a17b581bd6d
-- name    : P2M_GlobalTheory_DetInv_PsiPhi_phiInv_frobenius__8a17b581bd6d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:18.088513+00:00
-- url     : https://prove2.me/theorems/93f4343d-57ed-4fe4-9646-c0b319393077
-- title:
--   P2 M Global Theory Det Inv Psi Phi phi Inv frobenius  8a17b581bd6d: P2 M Global Theory Det Inv Psi Phi phi Inv frobenius  8a17b581bd6d
-- statement:
--   The P2 M Global Theory Det Inv Psi Phi phi Inv frobenius  8a17b581bd6d construction uses the P2 M Global Theory Det Inv Psi Phi phi Inv frobenius  8a17b581bd6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOfPadic.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOfPadic.lean#L19-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusOfPadic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
open GlobalTheory GlobalTheory.DetInv GlobalTheory.DetInv.PsiPhi
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem P2M_GlobalTheory_DetInv_PsiPhi_phiInv_frobenius__8a17b581bd6d (a : Ainf p O) : phiInv p O (WittVector.frobenius a) = a := by sorry

alias «GlobalTheory».«DetInv».«PsiPhi».«phiInv_frobenius'» := P2M_GlobalTheory_DetInv_PsiPhi_phiInv_frobenius__8a17b581bd6d
