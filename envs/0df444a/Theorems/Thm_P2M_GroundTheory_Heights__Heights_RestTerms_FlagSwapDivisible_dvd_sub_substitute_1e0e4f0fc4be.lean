-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagSwapDivisible_dvd_sub_substitute_1e0e4f0fc4be
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagSwapDivisible_dvd_sub_substitute_1e0e4f0fc4be
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:19:52.353057+00:00
-- url     : https://prove2.me/theorems/749d0e5b-3870-4ae7-b2f0-d45d3c69302f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Swap Divisible dvd sub substitute 1e0e4f0fc4be: P2 M Ground Theory Heights  Heights Rest Terms Flag Swap Divisible dvd sub substitute 1e0e4f0fc4be
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Swap Divisible dvd sub substitute 1e0e4f0fc4be construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Swap Divisible dvd sub substitute 1e0e4f0fc4be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagSwapDivisible.lean#L13-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagSwapDivisible.lean#L13-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagSwapDivisible
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagSwapDivisible_dvd_sub_substitute_1e0e4f0fc4be {R σ : Type} [CommRing R] [DecidableEq σ] (a b : σ)
    (Q : MvPolynomial σ R) :
    (X a - X b : MvPolynomial σ R) ∣
      Q - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagSwapDivisible».«dvd_sub_substitute» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagSwapDivisible_dvd_sub_substitute_1e0e4f0fc4be
