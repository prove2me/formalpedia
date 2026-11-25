-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DetInv_PsiPhi_frobenius_phiInv__7e3fdf573703
-- name    : P2M_GlobalTheory_DetInv_PsiPhi_frobenius_phiInv__7e3fdf573703
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:24.85257+00:00
-- url     : https://prove2.me/theorems/0514bd13-b0ee-4ecd-a4e8-48b3fb312bda
-- title:
--   P2 M Global Theory Det Inv Psi Phi frobenius phi Inv  7e3fdf573703: P2 M Global Theory Det Inv Psi Phi frobenius phi Inv  7e3fdf573703
-- statement:
--   The P2 M Global Theory Det Inv Psi Phi frobenius phi Inv  7e3fdf573703 construction uses the P2 M Global Theory Det Inv Psi Phi frobenius phi Inv  7e3fdf573703 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOfPadic.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOfPadic.lean#L13-L17

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

theorem P2M_GlobalTheory_DetInv_PsiPhi_frobenius_phiInv__7e3fdf573703 (a : Ainf p O) : WittVector.frobenius (phiInv p O a) = a := by sorry

alias «GlobalTheory».«DetInv».«PsiPhi».«frobenius_phiInv'» := P2M_GlobalTheory_DetInv_PsiPhi_frobenius_phiInv__7e3fdf573703
