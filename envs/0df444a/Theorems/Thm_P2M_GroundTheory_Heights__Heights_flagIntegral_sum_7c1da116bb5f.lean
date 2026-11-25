-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_flagIntegral_sum_7c1da116bb5f
-- name    : P2M_GroundTheory_Heights__Heights_flagIntegral_sum_7c1da116bb5f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:32.197814+00:00
-- url     : https://prove2.me/theorems/30b36676-fcb9-4b58-8d03-1cf4a0005592
-- title:
--   P2 M Ground Theory Heights  Heights flag Integral sum 7c1da116bb5f: P2 M Ground Theory Heights  Heights flag Integral sum 7c1da116bb5f
-- statement:
--   The P2 M Ground Theory Heights  Heights flag Integral sum 7c1da116bb5f construction uses the P2 M Ground Theory Heights  Heights flag Integral sum 7c1da116bb5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutFlagKillsIdeal.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutFlagKillsIdeal.lean#L9-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutFlagKillsIdeal
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
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_flagIntegral_sum_7c1da116bb5f {ι : Type*} (f N : ℕ) (s : Finset ι)
    (P : ι → RestTerms.RootRing f N) :
    RestTerms.flagIntegral f N (∑ i ∈ s, P i) = ∑ i ∈ s, RestTerms.flagIntegral f N (P i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«flagIntegral_sum» := P2M_GroundTheory_Heights__Heights_flagIntegral_sum_7c1da116bb5f
