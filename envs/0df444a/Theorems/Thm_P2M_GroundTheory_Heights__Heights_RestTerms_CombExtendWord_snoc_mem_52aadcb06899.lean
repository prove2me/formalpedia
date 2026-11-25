-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombExtendWord_snoc_mem_52aadcb06899
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_CombExtendWord_snoc_mem_52aadcb06899
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:04:55.200686+00:00
-- url     : https://prove2.me/theorems/30f99bc7-59f4-4690-ac1f-4fd0901ea3e9
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb Extend Word snoc mem 52aadcb06899: P2 M Ground Theory Heights  Heights Rest Terms Comb Extend Word snoc mem 52aadcb06899
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb Extend Word snoc mem 52aadcb06899 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb Extend Word snoc mem 52aadcb06899 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombExtendWord.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombExtendWord.lean#L15-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombExtendWord
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
open Finset Comb
noncomputable section
open scoped Classical
open GroundTheory.Heights₂.Heights.RestTerms.CombExtendWord

theorem P2M_GroundTheory_Heights__Heights_RestTerms_CombExtendWord_snoc_mem_52aadcb06899 {m n : ℕ} (lam : Fin m → ℕ) (hlam : Antitone lam) (k : Fin m) (hk : 1 ≤ lam k)
    (v : Fin n → Fin m) (hv : v ∈ latticeWords n (Function.update lam k (lam k - 1))) :
    (Fin.snoc v k : Fin (n + 1) → Fin m) ∈ latticeWords (n + 1) lam := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«CombExtendWord».«snoc_mem» := P2M_GroundTheory_Heights__Heights_RestTerms_CombExtendWord_snoc_mem_52aadcb06899
