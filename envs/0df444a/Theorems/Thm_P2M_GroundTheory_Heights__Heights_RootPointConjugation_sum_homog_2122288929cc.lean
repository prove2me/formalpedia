-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointConjugation_sum_homog_2122288929cc
-- name    : P2M_GroundTheory_Heights__Heights_RootPointConjugation_sum_homog_2122288929cc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:36:59.128651+00:00
-- url     : https://prove2.me/theorems/d8478b3f-8ec9-4e3a-9462-ada7cc585646
-- title:
--   P2 M Ground Theory Heights  Heights Root Point Conjugation sum homog 2122288929cc: P2 M Ground Theory Heights  Heights Root Point Conjugation sum homog 2122288929cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Point Conjugation sum homog 2122288929cc construction uses the P2 M Ground Theory Heights  Heights Root Point Conjugation sum homog 2122288929cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointConj.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointConj.lean#L20-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointConj
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
open GroundTheory.Heights₂.Heights.RootPointConjugation

theorem P2M_GroundTheory_Heights__Heights_RootPointConjugation_sum_homog_2122288929cc {σ A : Type*} [CommRing A] (S : Finset (σ →₀ ℕ)) (N : ℕ)
    (hS : ∀ μ ∈ S, (μ.sum fun _ e => e) ≤ N) (s : A) (g : (σ →₀ ℕ) → A) :
    ∑ μ ∈ S, s ^ (N - μ.sum fun _ e => e) * (s ^ (μ.sum fun _ e => e) * g μ) = s ^ N * ∑ μ ∈ S, g μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootPointConjugation».«sum_homog» := P2M_GroundTheory_Heights__Heights_RootPointConjugation_sum_homog_2122288929cc
