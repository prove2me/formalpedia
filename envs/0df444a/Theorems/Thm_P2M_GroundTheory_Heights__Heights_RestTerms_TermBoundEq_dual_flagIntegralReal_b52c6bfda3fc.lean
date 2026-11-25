-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_dual_flagIntegralReal_b52c6bfda3fc
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_dual_flagIntegralReal_b52c6bfda3fc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:21:04.488817+00:00
-- url     : https://prove2.me/theorems/dd16415f-ad39-483f-9a1b-f34c8be65347
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq dual flag Integral Real b52c6bfda3fc: P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq dual flag Integral Real b52c6bfda3fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq dual flag Integral Real b52c6bfda3fc construction uses the P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq dual flag Integral Real b52c6bfda3fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealRootRingToRealAlt.lean#L58-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealRootRingToRealAlt.lean#L58-L70

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
variable {σ : Type*} (φ : Module.Dual ℚ ℝ)

theorem P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_dual_flagIntegralReal_b52c6bfda3fc (f N : ℕ) (P : MvPolynomial (Fin f × Fin N) ℝ) :
    φ (flagIntegralReal f N P) = flagIntegral f N (coeffMap φ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«TermBoundEq».«dual_flagIntegralReal» := P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_dual_flagIntegralReal_b52c6bfda3fc
