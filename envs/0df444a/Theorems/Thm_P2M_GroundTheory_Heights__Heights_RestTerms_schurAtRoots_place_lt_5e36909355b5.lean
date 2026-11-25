-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_schurAtRoots_place_lt_5e36909355b5
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_schurAtRoots_place_lt_5e36909355b5
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:37:09.419967+00:00
-- url     : https://prove2.me/theorems/4702e7f5-2033-54ac-a2a5-f7bbb743d093
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms schur At Roots place lt 5e36909355b5: P2 M Ground Theory Heights  Heights Rest Terms schur At Roots place lt 5e36909355b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms schur At Roots place lt 5e36909355b5 construction uses the P2 M Ground Theory Heights  Heights Rest Terms schur At Roots place lt 5e36909355b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSchurAtRootsOfUnity.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSchurAtRootsOfUnity.lean#L12-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSchurAtRootsOfUnity
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_schurAtRoots_place_lt_5e36909355b5 {r k : ℕ} (nu : Fin r → ℕ) (hanti : Antitone nu)
    (hsum : ∑ i, nu i = k) (i : Fin r) (hi : 1 ≤ nu i) : (i : ℕ) < k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«schurAtRoots_place_lt» := P2M_GroundTheory_Heights__Heights_RestTerms_schurAtRoots_place_lt_5e36909355b5
