-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_flagIntegralReal_rootRingToReal_7e4d0bc52d89
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_flagIntegralReal_rootRingToReal_7e4d0bc52d89
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:21:28.711869+00:00
-- url     : https://prove2.me/theorems/5a26dfa2-94be-45e1-928b-af7cc52c6ff9
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq flag Integral Real root Ring To Real 7e4d0bc52d89: P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq flag Integral Real root Rin
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq flag Integral Real root Ring To Real 7e4d0bc52d89 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq flag Integral Real root Ring To Real 7e4d0bc52d89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealRootRingToRealAlt.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealRootRingToRealAlt.lean#L14-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
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
open GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_flagIntegralReal_rootRingToReal_7e4d0bc52d89 (f N j k : ℕ) (h : N = j + k) (P : RootRing f N) :
    flagIntegralReal f (j + k) (rootRingToReal f N j k h P) = (flagIntegral f N P : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«TermBoundEq».«flagIntegralReal_rootRingToReal» := P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_flagIntegralReal_rootRingToReal_7e4d0bc52d89
