-- Prove2me | Theorems.Thm_P2M_RH_P2M_GroundTheory_Heights__Heights_RestTerms_symmetricGroupCharacter_eq_cf_ddc4362c6d08_01d69069a647955c
-- name    : P2M_RH_P2M_GroundTheory_Heights__Heights_RestTerms_symmetricGroupCharacter_eq_cf_ddc4362c6d08_01d69069a647955c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:05:23.971511+00:00
-- url     : https://prove2.me/theorems/ad00fd6f-0f9e-57c4-afed-505e08434c74
-- title:
--   P2 M RH P2 M Ground Theory Heights  Heights Rest Terms symmetric Group Character eq cf ddc4362c6d08 01d69069a647955c: P2 M RH P2 M Ground Theory Heights  Heights Rest Terms symmetric Group Character e
-- statement:
--   The P2 M RH P2 M Ground Theory Heights  Heights Rest Terms symmetric Group Character eq cf ddc4362c6d08 01d69069a647955c construction uses the P2 M RH P2 M Ground Theory Heights  Heights Rest Terms symmetric Group Character eq cf ddc4362c6d08 01d69069a647955c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCharacterBound.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCharacterBound.lean#L11-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCharacterBound
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

theorem P2M_RH_P2M_GroundTheory_Heights__Heights_RestTerms_symmetricGroupCharacter_eq_cf_ddc4362c6d08_01d69069a647955c {m : ℕ} (lam : Fin m → ℕ) (rho : List ℕ) :
    symmetricGroupCharacter lam rho = cf (fun i => lam i + stair m i) (alternantPsum m rho) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«symmetricGroupCharacter_eq_cf» := P2M_RH_P2M_GroundTheory_Heights__Heights_RestTerms_symmetricGroupCharacter_eq_cf_ddc4362c6d08_01d69069a647955c
