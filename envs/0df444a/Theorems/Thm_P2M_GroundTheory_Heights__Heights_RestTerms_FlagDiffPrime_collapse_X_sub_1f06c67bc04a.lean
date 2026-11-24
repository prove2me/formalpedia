-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_collapse_X_sub_1f06c67bc04a
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_collapse_X_sub_1f06c67bc04a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:58.980849+00:00
-- url     : https://prove2.me/theorems/5b701228-dc14-4d9a-8717-56464385f6ca
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime collapse X sub 1f06c67bc04a: P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime collapse X sub 1f06c67bc04a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime collapse X sub 1f06c67bc04a construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime collapse X sub 1f06c67bc04a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagDiffPrime.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagDiffPrime.lean#L20-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagDiffPrime
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagDiffPrime
variable {σ : Type} [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_collapse_X_sub_1f06c67bc04a (a b : σ) : collapse a b (X a - X b : MvPolynomial σ ℚ) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagDiffPrime».«collapse_X_sub» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_collapse_X_sub_1f06c67bc04a
