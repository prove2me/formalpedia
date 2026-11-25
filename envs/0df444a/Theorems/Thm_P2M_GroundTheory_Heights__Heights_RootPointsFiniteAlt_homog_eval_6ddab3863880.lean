-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_homog_eval_6ddab3863880
-- name    : P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_homog_eval_6ddab3863880
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:18.397808+00:00
-- url     : https://prove2.me/theorems/ce364cb4-7b61-44e7-aa84-8b500efb8403
-- title:
--   P2 M Ground Theory Heights  Heights Root Points Finite Alt homog eval 6ddab3863880: P2 M Ground Theory Heights  Heights Root Points Finite Alt homog eval 6ddab3863880
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Points Finite Alt homog eval 6ddab3863880 construction uses the P2 M Ground Theory Heights  Heights Root Points Finite Alt homog eval 6ddab3863880 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointsFinite.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointsFinite.lean#L37-L45

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

theorem P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_homog_eval_6ddab3863880 (z : (Σ k, ι k) → ℂ) (p a : Σ k, ι k) (hza : z a ≠ 0) (q : Polynomial ℤ) :
    eval z (map (Int.castRingHom ℂ) (homog q p a)) =
      z a ^ q.natDegree * q.eval₂ (Int.castRingHom ℂ) (z p / z a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootPointsFiniteAlt».«homog_eval» := P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_homog_eval_6ddab3863880
