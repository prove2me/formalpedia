-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_LemmaA_hypotheses_inhabited_db910e8699fe
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_LemmaA_hypotheses_inhabited_db910e8699fe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:42.590907+00:00
-- url     : https://prove2.me/theorems/e1633e2e-6eaf-4b9f-9f56-49664d77a3e0
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Lemma A hypotheses inhabited db910e8699fe: P2 M Ground Theory Heights  Heights Rest Terms Lemma A hypotheses inhabited db910e8699fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Lemma A hypotheses inhabited db910e8699fe construction uses the P2 M Ground Theory Heights  Heights Rest Terms Lemma A hypotheses inhabited db910e8699fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Statements.lean#L390-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Statements.lean#L390-L395

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_LemmaA_hypotheses_inhabited_db910e8699fe :
    IsPowerSumDecomposition 1 1 (blockPowerSum 1 1 1 0)
        (fun k τ => if k = 1 ∧ τ = 0 then 1 else 0) ∧
      (1 : RootRing 1 1).IsHomogeneous (1 - 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«LemmaA».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_RestTerms_LemmaA_hypotheses_inhabited_db910e8699fe
