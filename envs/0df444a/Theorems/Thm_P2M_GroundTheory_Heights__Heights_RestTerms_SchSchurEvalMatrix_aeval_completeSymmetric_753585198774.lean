-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchSchurEvalMatrix_aeval_completeSymmetric_753585198774
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchSchurEvalMatrix_aeval_completeSymmetric_753585198774
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:20:19.472033+00:00
-- url     : https://prove2.me/theorems/089eeb99-db8e-47c6-b630-e922a1e2f7cb
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Schur Eval Matrix aeval complete Symmetric 753585198774: P2 M Ground Theory Heights  Heights Rest Terms Sch Schur Eval Matrix aeval complete Symmetri
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Schur Eval Matrix aeval complete Symmetric 753585198774 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Schur Eval Matrix aeval complete Symmetric 753585198774 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSchurEvalMatrix.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSchurEvalMatrix.lean#L12-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSchurEvalMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchSchurEvalMatrix_aeval_completeSymmetric_753585198774 (h1 : SchCompleteAtRootsOfUnity.Statement)
    (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (d : ℤ) :
    aeval (rootOfUnityPoint N k) (completeSymmetric (Fin N) d) =
      if 0 ≤ d ∧ (k : ℤ) ∣ d then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchSchurEvalMatrix».«aeval_completeSymmetric» := P2M_GroundTheory_Heights__Heights_RestTerms_SchSchurEvalMatrix_aeval_completeSymmetric_753585198774
