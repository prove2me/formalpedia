-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointConjugation_aeval_mul_monomial_c5929ecdffff
-- name    : P2M_GroundTheory_Heights__Heights_RootPointConjugation_aeval_mul_monomial_c5929ecdffff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:36:55.566143+00:00
-- url     : https://prove2.me/theorems/7889595e-0c6d-480e-9245-2c2ebd70cfad
-- title:
--   P2 M Ground Theory Heights  Heights Root Point Conjugation aeval mul monomial c5929ecdffff: P2 M Ground Theory Heights  Heights Root Point Conjugation aeval mul monomial c5929ecdffff
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Point Conjugation aeval mul monomial c5929ecdffff construction uses the P2 M Ground Theory Heights  Heights Root Point Conjugation aeval mul monomial c5929ecdffff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointConj.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointConj.lean#L14-L18

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

theorem P2M_GroundTheory_Heights__Heights_RootPointConjugation_aeval_mul_monomial_c5929ecdffff {σ A : Type*} [CommRing A] (s : A) (x : σ → A) (μ : σ →₀ ℕ) (c : ℤ) :
    aeval (fun i => s * x i) (monomial μ c) = s ^ (μ.sum fun _ e => e) * aeval x (monomial μ c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootPointConjugation».«aeval_mul_monomial» := P2M_GroundTheory_Heights__Heights_RootPointConjugation_aeval_mul_monomial_c5929ecdffff
