-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_gaussNorm_map_eq_one_4c5bd7b79347
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_gaussNorm_map_eq_one_4c5bd7b79347
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:44.33774+00:00
-- url     : https://prove2.me/theorems/5fc862fa-a092-5df3-bce4-13fc9ce441c1
-- title:
--   P2 M Ground Theory Heights  Heights Vertical gauss Norm map eq one 4c5bd7b79347: P2 M Ground Theory Heights  Heights Vertical gauss Norm map eq one 4c5bd7b79347
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical gauss Norm map eq one 4c5bd7b79347 construction uses the P2 M Ground Theory Heights  Heights Vertical gauss Norm map eq one 4c5bd7b79347 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussEq.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussEq.lean#L40-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_gaussNorm_map_eq_one_4c5bd7b79347 {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {σ : Type*} (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«gaussNorm_map_eq_one» := P2M_GroundTheory_Heights__Heights_Vertical_gaussNorm_map_eq_one_4c5bd7b79347
