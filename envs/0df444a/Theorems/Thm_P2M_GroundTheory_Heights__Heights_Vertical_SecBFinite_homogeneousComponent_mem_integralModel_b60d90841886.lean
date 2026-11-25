-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_homogeneousComponent_mem_integralModel_b60d90841886
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_homogeneousComponent_mem_integralModel_b60d90841886
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:42:50.064341+00:00
-- url     : https://prove2.me/theorems/0b993aa5-1201-4527-b63a-367f77a02e4b
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite homogeneous Component mem integral Model b60d90841886: P2 M Ground Theory Heights  Heights Vertical Sec BFinite homogeneous Component mem integ
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite homogeneous Component mem integral Model b60d90841886 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite homogeneous Component mem integral Model b60d90841886 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L148-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L148-L153

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
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_homogeneousComponent_mem_integralModel_b60d90841886 {n : ℕ} {I : Ideal (MvPolynomial (Fin n) K)}
    (hI : IsHomogIdeal I) : ∀ p ∈ integralModel I, ∀ d, homogeneousComponent d p ∈ integralModel I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«homogeneousComponent_mem_integralModel» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_homogeneousComponent_mem_integralModel_b60d90841886
