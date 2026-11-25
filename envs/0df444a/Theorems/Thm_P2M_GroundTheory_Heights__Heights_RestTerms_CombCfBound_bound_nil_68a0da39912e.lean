-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_bound_nil_68a0da39912e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_bound_nil_68a0da39912e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:04:51.440322+00:00
-- url     : https://prove2.me/theorems/c04492a0-40fc-5033-a8cc-4db999a9cedb
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Bound bound nil 68a0da39912e: P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Bound bound nil 68a0da39912e
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Bound bound nil 68a0da39912e construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Bound bound nil 68a0da39912e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCfBound.lean#L34-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCfBound.lean#L34-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfBound
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
open MvPolynomial Finset Equiv Comb
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.CombCfBound

theorem P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_bound_nil_68a0da39912e (m : ℕ) (lam : Fin m → ℕ) (hlam : Antitone lam) :
    |cf (fun i => lam i + stair m i) (alternantPsum m [])| ≤ ((latticeWords 0 lam).card : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«CombCfBound».«bound_nil» := P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_bound_nil_68a0da39912e
