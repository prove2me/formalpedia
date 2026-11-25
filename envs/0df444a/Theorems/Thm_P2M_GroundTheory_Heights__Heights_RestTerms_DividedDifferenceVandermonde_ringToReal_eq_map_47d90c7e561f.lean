-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_DividedDifferenceVandermonde_ringToReal_eq_map_47d90c7e561f
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_DividedDifferenceVandermonde_ringToReal_eq_map_47d90c7e561f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:20:23.524718+00:00
-- url     : https://prove2.me/theorems/2d42e2e7-0f4b-4336-b07e-322a63ea9407
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Divided Difference Vandermonde ring To Real eq map 47d90c7e561f: P2 M Ground Theory Heights  Heights Rest Terms Divided Difference Vandermonde ring To Re
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Divided Difference Vandermonde ring To Real eq map 47d90c7e561f construction uses the P2 M Ground Theory Heights  Heights Rest Terms Divided Difference Vandermonde ring To Real eq map 47d90c7e561f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AntisymmetrizeBlockVandermondeOf.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AntisymmetrizeBlockVandermondeOf.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AntisymmetrizeBlockVandermondeOf
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
open GroundTheory.Heights₂.Heights.RestTerms.DividedDifferenceVandermonde

theorem P2M_GroundTheory_Heights__Heights_RestTerms_DividedDifferenceVandermonde_ringToReal_eq_map_47d90c7e561f (f j k : ℕ) (Φ : RootRing f (j + k)) :
    rootRingToReal f (j + k) j k rfl Φ = map (algebraMap ℚ ℝ) Φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«DividedDifferenceVandermonde».«ringToReal_eq_map» := P2M_GroundTheory_Heights__Heights_RestTerms_DividedDifferenceVandermonde_ringToReal_eq_map_47d90c7e561f
