-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_prod_one_sub_rootOfUnityPoint_80e9c307bf5e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_prod_one_sub_rootOfUnityPoint_80e9c307bf5e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:18.4018+00:00
-- url     : https://prove2.me/theorems/ea7faaa8-a8a8-43d4-9dce-bbad38e6194b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms prod one sub root Of Unity Point 80e9c307bf5e: P2 M Ground Theory Heights  Heights Rest Terms prod one sub root Of Unity Point 80e9c307bf5e
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms prod one sub root Of Unity Point 80e9c307bf5e construction uses the P2 M Ground Theory Heights  Heights Rest Terms prod one sub root Of Unity Point 80e9c307bf5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchCompleteAtRootsOfUnity.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchCompleteAtRootsOfUnity.lean#L10-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchCompleteAtRootsOfUnity
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_prod_one_sub_rootOfUnityPoint_80e9c307bf5e (h1 : SchProdOneSubRootsOfUnity.Statement) {N k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∏ i : Fin N, (1 - Polynomial.C (rootOfUnityPoint N k i) * Polynomial.X) =
      (1 - Polynomial.X ^ k : Polynomial ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«prod_one_sub_rootOfUnityPoint» := P2M_GroundTheory_Heights__Heights_RestTerms_prod_one_sub_rootOfUnityPoint_80e9c307bf5e
