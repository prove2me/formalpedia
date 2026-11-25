-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_isIntegral_of_pow_eq_one_2609fb7d6df2
-- name    : P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_isIntegral_of_pow_eq_one_2609fb7d6df2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:58.221851+00:00
-- url     : https://prove2.me/theorems/861a2c8d-7fcb-5b04-b68a-814b2a74aad8
-- title:
--   P2 M Ground Theory Heights  Heights Root Points Finite Alt is Integral of pow eq one 2609fb7d6df2: P2 M Ground Theory Heights  Heights Root Points Finite Alt is Integral of pow eq one 2609fb7d6df2
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Points Finite Alt is Integral of pow eq one 2609fb7d6df2 construction uses the P2 M Ground Theory Heights  Heights Root Points Finite Alt is Integral of pow eq one 2609fb7d6df2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointsFinite.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointsFinite.lean#L47-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointsFinite
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootPointsFiniteAlt
variable {K : Type*} {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_isIntegral_of_pow_eq_one_2609fb7d6df2 {x : ℂ} {k : ℕ} (hk : 0 < k) (hx : x ^ k = 1) : IsIntegral ℤ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootPointsFiniteAlt».«isIntegral_of_pow_eq_one» := P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_isIntegral_of_pow_eq_one_2609fb7d6df2
