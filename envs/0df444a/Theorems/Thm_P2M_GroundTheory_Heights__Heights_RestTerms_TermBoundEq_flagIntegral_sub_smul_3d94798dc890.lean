-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_flagIntegral_sub_smul_3d94798dc890
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_flagIntegral_sub_smul_3d94798dc890
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:22:14.175712+00:00
-- url     : https://prove2.me/theorems/b2a975f9-c98d-4f53-96f2-59a861fd222d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq flag Integral sub smul 3d94798dc890: P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq flag Integral sub smul 3d94798dc890
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq flag Integral sub smul 3d94798dc890 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq flag Integral sub smul 3d94798dc890 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealRootRingToRealAlt.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealRootRingToRealAlt.lean#L72-L77

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_flagIntegral_sub_smul_3d94798dc890 (f N : ℕ) (A B : RootRing f N) (s : ℚ) :
    flagIntegral f N (A - s • B) = flagIntegral f N A - s * flagIntegral f N B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«TermBoundEq».«flagIntegral_sub_smul» := P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_flagIntegral_sub_smul_3d94798dc890
