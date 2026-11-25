-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_parToFrac_algebraMap_ee484fc0a399
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_parToFrac_algebraMap_ee484fc0a399
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:38.553603+00:00
-- url     : https://prove2.me/theorems/21ded0d2-ef80-4179-9a39-68a08ddb2b2f
-- title:
--   P2 M Ground Theory Heights  Heights Vertical par To Frac algebra Map ee484fc0a399: P2 M Ground Theory Heights  Heights Vertical par To Frac algebra Map ee484fc0a399
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical par To Frac algebra Map ee484fc0a399 construction uses the P2 M Ground Theory Heights  Heights Vertical par To Frac algebra Map ee484fc0a399 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBLinInj.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBLinInj.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBLinInj
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

theorem P2M_GroundTheory_Heights__Heights_Vertical_parToFrac_algebraMap_ee484fc0a399 {K : Type*} [Field K] [NumberField K] (e n : ℕ)
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    parToFrac e n v (algebraMap (𝓞 K) (ParDVR e n v) x) = kToFrac K e n (algebraMap (𝓞 K) K x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«parToFrac_algebraMap» := P2M_GroundTheory_Heights__Heights_Vertical_parToFrac_algebraMap_ee484fc0a399
