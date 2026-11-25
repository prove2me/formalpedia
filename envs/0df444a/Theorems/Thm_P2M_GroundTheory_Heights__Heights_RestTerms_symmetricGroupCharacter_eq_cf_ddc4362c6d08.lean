-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_symmetricGroupCharacter_eq_cf_ddc4362c6d08
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_symmetricGroupCharacter_eq_cf_ddc4362c6d08
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:04:38.038393+00:00
-- url     : https://prove2.me/theorems/5abea2cf-dc88-4d34-8eff-a13c586c3654
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms symmetric Group Character eq cf ddc4362c6d08: P2 M Ground Theory Heights  Heights Rest Terms symmetric Group Character eq cf ddc4362c6d08
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms symmetric Group Character eq cf ddc4362c6d08 construction uses the P2 M Ground Theory Heights  Heights Rest Terms symmetric Group Character eq cf ddc4362c6d08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCharacterAtIdentity.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCharacterAtIdentity.lean#L11-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCharacterAtIdentity
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
open MvPolynomial Finset Comb
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_symmetricGroupCharacter_eq_cf_ddc4362c6d08 {m : ℕ} (lam : Fin m → ℕ) (rho : List ℕ) :
    symmetricGroupCharacter lam rho =
      cf (fun i => lam i + stair m i) (alternantPsum m rho) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«symmetricGroupCharacter_eq_cf» := P2M_GroundTheory_Heights__Heights_RestTerms_symmetricGroupCharacter_eq_cf_ddc4362c6d08
