-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_eq_zero_of_C_mem_integralModel_e1513c1896ee
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_eq_zero_of_C_mem_integralModel_e1513c1896ee
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:43:36.976469+00:00
-- url     : https://prove2.me/theorems/7d00d7ef-a72d-4a2d-94f4-78d26cf5f1b1
-- title:
--   P2 M Ground Theory Heights  Heights Vertical eq zero of C mem integral Model e1513c1896ee: P2 M Ground Theory Heights  Heights Vertical eq zero of C mem integral Model e1513c1896ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical eq zero of C mem integral Model e1513c1896ee construction uses the P2 M Ground Theory Heights  Heights Vertical eq zero of C mem integral Model e1513c1896ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PVertSpec.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PVertSpec.lean#L41-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PVertSpec
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
variable {K : Type*} [Field K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_eq_zero_of_C_mem_integralModel_e1513c1896ee {I : Ideal (MvPolynomial (Fin n) K)} (hI : I.IsPrime)
    {c : 𝓞 K} (hc : C c ∈ integralModel I) : c = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«eq_zero_of_C_mem_integralModel» := P2M_GroundTheory_Heights__Heights_Vertical_eq_zero_of_C_mem_integralModel_e1513c1896ee
