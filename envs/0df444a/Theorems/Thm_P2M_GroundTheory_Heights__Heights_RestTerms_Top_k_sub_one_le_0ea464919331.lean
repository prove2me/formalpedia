-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_k_sub_one_le_0ea464919331
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_k_sub_one_le_0ea464919331
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:49.286726+00:00
-- url     : https://prove2.me/theorems/b86d5146-a17b-5b68-a95c-a5f9c0a242c2
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top k sub one le 0ea464919331: P2 M Ground Theory Heights  Heights Rest Terms Top k sub one le 0ea464919331
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top k sub one le 0ea464919331 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top k sub one le 0ea464919331 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/POtherFactorFormula.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/POtherFactorFormula.lean#L29-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_POtherFactorFormula
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_k_sub_one_le_0ea464919331 (r a k : ℕ) (hr : 1 ≤ r) (ha : 1 ≤ a) (hk : k ≤ r + a) : k - 1 ≤ r * a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«k_sub_one_le» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_k_sub_one_le_0ea464919331
