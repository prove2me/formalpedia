-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_unit_mul_star_eq_norm_2958366fd685
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_unit_mul_star_eq_norm_2958366fd685
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:19:22.757793+00:00
-- url     : https://prove2.me/theorems/b6ac4a83-b9b6-43d9-968b-61ccabcaeb65
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume exists unit mul star eq norm 2958366fd685: P2 M Ground Theory Heights  Heights Finite Covolume exists unit mul star eq norm 2958366fd685
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume exists unit mul star eq norm 2958366fd685 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume exists unit mul star eq norm 2958366fd685 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PEigenReflectionMaps.lean#L21-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PEigenReflectionMaps.lean#L21-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PEigenReflectionMaps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
open scoped ComplexOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_unit_mul_star_eq_norm_2958366fd685 (s : ℂ) : ∃ α : ℂ, ‖α‖ = 1 ∧ α * star s = ‖s‖ ∧ star α * s = ‖s‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«exists_unit_mul_star_eq_norm» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_unit_mul_star_eq_norm_2958366fd685
