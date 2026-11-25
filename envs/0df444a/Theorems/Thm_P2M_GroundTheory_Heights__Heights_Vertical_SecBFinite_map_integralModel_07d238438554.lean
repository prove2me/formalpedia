-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_map_integralModel_07d238438554
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_map_integralModel_07d238438554
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:57.040906+00:00
-- url     : https://prove2.me/theorems/ed8a2a7c-8fa3-4c52-a4ba-f5cfe6ea5786
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite map integral Model 07d238438554: P2 M Ground Theory Heights  Heights Vertical Sec BFinite map integral Model 07d238438554
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite map integral Model 07d238438554 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite map integral Model 07d238438554 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L121-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L121-L144

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
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
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_map_integralModel_07d238438554 {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) :
    (integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) K)) = I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«map_integralModel» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_map_integralModel_07d238438554
