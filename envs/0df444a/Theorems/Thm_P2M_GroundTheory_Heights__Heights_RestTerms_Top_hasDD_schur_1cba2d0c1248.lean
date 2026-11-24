-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_1cba2d0c1248
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_1cba2d0c1248
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:25.546969+00:00
-- url     : https://prove2.me/theorems/f03a63c6-267d-4a03-9213-29ef7a694995
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top has DD schur 1cba2d0c1248: P2 M Ground Theory Heights  Heights Rest Terms Top has DD schur 1cba2d0c1248
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top has DD schur 1cba2d0c1248 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top has DD schur 1cba2d0c1248 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L256-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L256-L264

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_1cba2d0c1248 (hB : LemmaB.Statement) (r a : ℕ) (c : SmallBlock) :
    ∃ κ : ℚ, (κ = (r.factorial : ℚ) * a.factorial ∨ κ = -((r.factorial : ℚ) * a.factorial)) ∧
      ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«hasDD_schur» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_1cba2d0c1248
