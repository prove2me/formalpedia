-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_flagIntegral_add_smul_15ff1eab2e68
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_flagIntegral_add_smul_15ff1eab2e68
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:51.144295+00:00
-- url     : https://prove2.me/theorems/7c3e1fce-ca5f-4605-bd93-fb8723d6d149
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq flag Integral add smul 15ff1eab2e68: P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq flag Integral add smul 15ff1eab2e68
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq flag Integral add smul 15ff1eab2e68 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq flag Integral add smul 15ff1eab2e68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealTransferOfSyzygy.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealTransferOfSyzygy.lean#L27-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealTransferOfSyzygy
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
open GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_flagIntegral_add_smul_15ff1eab2e68 (f N : ℕ) (A B : RootRing f N) (t : ℚ) :
    flagIntegral f N (A + t • B) = flagIntegral f N A + t * flagIntegral f N B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«RestBoundEq».«flagIntegral_add_smul» := P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_flagIntegral_add_smul_15ff1eab2e68
