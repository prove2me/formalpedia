-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_chart_sum_eq_one_0a97e722f90e
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_chart_sum_eq_one_0a97e722f90e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:16.33492+00:00
-- url     : https://prove2.me/theorems/eff51fba-6efc-56b4-8a71-cf03817b86c4
-- title:
--   P2 M Ground Theory Heights  Heights Vertical chart sum eq one 0a97e722f90e: P2 M Ground Theory Heights  Heights Vertical chart sum eq one 0a97e722f90e
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical chart sum eq one 0a97e722f90e construction uses the P2 M Ground Theory Heights  Heights Vertical chart sum eq one 0a97e722f90e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L69-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormIdentity
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
variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_chart_sum_eq_one_0a97e722f90e {R : Type*} [CommRing R] {Q : Ideal (MvPolynomial (Fin n) R)}
    {y : Par e n → R} : ∑ j, algebraMap R (SecAlg Q y) (y (.inr j)) * secCoord Q y j = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«chart_sum_eq_one» := P2M_GroundTheory_Heights__Heights_Vertical_chart_sum_eq_one_0a97e722f90e
