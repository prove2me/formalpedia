-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_syzygy_term_zero_de0130de93cd
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_syzygy_term_zero_de0130de93cd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:21:01.775856+00:00
-- url     : https://prove2.me/theorems/bd6f0594-e5f9-4bc8-94ad-606555e8ed45
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq syzygy term zero de0130de93cd: P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq syzygy term zero de0130de93cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq syzygy term zero de0130de93cd construction uses the P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq syzygy term zero de0130de93cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealTransferOfSyzygy.lean#L34-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealTransferOfSyzygy.lean#L34-L180

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_syzygy_term_zero_de0130de93cd (hA : RestBound.Statement) (f r a : ℕ) (c : SmallBlock)
    (hf : 1 ≤ f) (hr : 1 ≤ r) (ha : 1 ≤ a) (S : ℕ → Fin f → RootRing f (r + a))
    (hS : IsPowerSumDecomposition f (r + a) 0 S) (τ τ' : Fin f) (m : ℕ) (hm2 : 2 ≤ m)
    (hmN : m ≤ r + a) :
    flagIntegral f (r + a) (smallPowerSum f r a c (m - 1) τ' * S m τ) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«RestBoundEq».«syzygy_term_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_syzygy_term_zero_de0130de93cd
