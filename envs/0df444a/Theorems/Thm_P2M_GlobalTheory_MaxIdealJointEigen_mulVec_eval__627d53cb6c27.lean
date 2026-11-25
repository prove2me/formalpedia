-- Prove2me | Theorems.Thm_P2M_GlobalTheory_MaxIdealJointEigen_mulVec_eval__627d53cb6c27
-- name    : P2M_GlobalTheory_MaxIdealJointEigen_mulVec_eval__627d53cb6c27
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:37:00.558676+00:00
-- url     : https://prove2.me/theorems/daee18dc-acaf-5e09-8bee-2b76272acb72
-- title:
--   P2 M Global Theory Max Ideal Joint Eigen mul Vec eval  627d53cb6c27: P2 M Global Theory Max Ideal Joint Eigen mul Vec eval  627d53cb6c27
-- statement:
--   The P2 M Global Theory Max Ideal Joint Eigen mul Vec eval  627d53cb6c27 construction uses the P2 M Global Theory Max Ideal Joint Eigen mul Vec eval  627d53cb6c27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalIdealEqJointEigen.lean#L69-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalIdealEqJointEigen.lean#L69-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfIntegralMatrixUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalIdealEqJointEigen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory GlobalTheory.MaxIdealJointEigen

theorem P2M_GlobalTheory_MaxIdealJointEigen_mulVec_eval__627d53cb6c27 {O K I : Type} [CommRing O] [Field K] (emb : O →+* K) {n : ℕ}
    (ρ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O) (θ : I → K) (c : Fin n → K)
    (hc : ∀ i, ((ρ (X i)).map emb).mulVec c = θ i • c) (p : MvPolynomial I O) :
    ((ρ p).map emb).mulVec c = eval₂ emb θ p • c := by sorry

alias «GlobalTheory».«MaxIdealJointEigen».«mulVec_eval₂» := P2M_GlobalTheory_MaxIdealJointEigen_mulVec_eval__627d53cb6c27
