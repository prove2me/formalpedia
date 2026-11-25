-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_map_integralModel_0858299151ff
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_map_integralModel_0858299151ff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:48.359473+00:00
-- url     : https://prove2.me/theorems/4e126955-0f8d-404f-8e54-ef8503a0d31e
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BGeneric map integral Model 0858299151ff: P2 M Ground Theory Heights  Heights Vertical Sec BGeneric map integral Model 0858299151ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BGeneric map integral Model 0858299151ff construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BGeneric map integral Model 0858299151ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBGeneric.lean#L32-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBGeneric.lean#L32-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBGeneric
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
open GroundTheory.Heights₂.Heights.Vertical.SecBGeneric
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_map_integralModel_0858299151ff {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) :
    (integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) K)) = I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBGeneric».«map_integralModel» := P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_map_integralModel_0858299151ff
