-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_sameFactor_choose_le_ba79756e1d65
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_sameFactor_choose_le_ba79756e1d65
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:49.738317+00:00
-- url     : https://prove2.me/theorems/5d67c2fa-f522-5101-9776-3e9301636041
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms same Factor choose le ba79756e1d65: P2 M Ground Theory Heights  Heights Rest Terms same Factor choose le ba79756e1d65
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms same Factor choose le ba79756e1d65 construction uses the P2 M Ground Theory Heights  Heights Rest Terms same Factor choose le ba79756e1d65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorBound.lean#L30-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorBound.lean#L30-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorBound
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_sameFactor_choose_le_ba79756e1d65 (r a k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ r + a) :
    (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) / ((r * a : ℕ) + 1 : ℚ) ≤
      restX r a ^ (k - 1) / (k.factorial : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«sameFactor_choose_le» := P2M_GroundTheory_Heights__Heights_RestTerms_sameFactor_choose_le_ba79756e1d65
