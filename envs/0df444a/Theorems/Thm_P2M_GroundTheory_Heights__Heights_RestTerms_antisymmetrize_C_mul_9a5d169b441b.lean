-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_antisymmetrize_C_mul_9a5d169b441b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_antisymmetrize_C_mul_9a5d169b441b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:35:49.396798+00:00
-- url     : https://prove2.me/theorems/78eec8fd-ae7a-4bd4-a100-b1a14293df48
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms antisymmetrize C mul 9a5d169b441b: P2 M Ground Theory Heights  Heights Rest Terms antisymmetrize C mul 9a5d169b441b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms antisymmetrize C mul 9a5d169b441b construction uses the P2 M Ground Theory Heights  Heights Rest Terms antisymmetrize C mul 9a5d169b441b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PLemmaB.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PLemmaB.lean#L13-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PLemmaB
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_antisymmetrize_C_mul_9a5d169b441b (f N : ℕ) (k : ℚ) (H : RootRing f N) :
    antisymmetrize f N (C k * H) = C k * antisymmetrize f N H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«antisymmetrize_C_mul» := P2M_GroundTheory_Heights__Heights_RestTerms_antisymmetrize_C_mul_9a5d169b441b
