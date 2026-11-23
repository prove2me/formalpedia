-- Prove2me | Theorems.Thm_P2M_GlobalTheory_JR_NormalFormL_sum_mulVec__fc8d7b839a0b
-- name    : P2M_GlobalTheory_JR_NormalFormL_sum_mulVec__fc8d7b839a0b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:01.628803+00:00
-- url     : https://prove2.me/theorems/983e7f59-66e0-4c65-8a42-43465a4c03af
-- title:
--   P2 M Global Theory JR Normal Form L sum mul Vec  fc8d7b839a0b: P2 M Global Theory JR Normal Form L sum mul Vec  fc8d7b839a0b
-- statement:
--   The P2 M Global Theory JR Normal Form L sum mul Vec  fc8d7b839a0b construction uses the P2 M Global Theory JR Normal Form L sum mul Vec  fc8d7b839a0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L14-L19

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}

theorem P2M_GlobalTheory_JR_NormalFormL_sum_mulVec__fc8d7b839a0b {ι : Type} (s : Finset ι) (M : ι → Matrix (Fin r) (Fin r) k) (v : Fin r → k) :
    (∑ i ∈ s, M i) *ᵥ v = ∑ i ∈ s, M i *ᵥ v := by sorry

alias «GlobalTheory».«JR».«NormalFormL».«sum_mulVec'» := P2M_GlobalTheory_JR_NormalFormL_sum_mulVec__fc8d7b839a0b
