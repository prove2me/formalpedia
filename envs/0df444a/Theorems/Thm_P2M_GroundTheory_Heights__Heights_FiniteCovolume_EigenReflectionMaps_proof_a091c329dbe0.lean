-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_EigenReflectionMaps_proof_a091c329dbe0
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_EigenReflectionMaps_proof_a091c329dbe0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:56:29.726668+00:00
-- url     : https://prove2.me/theorems/b0eab98f-1496-527a-ae4e-c3ee85aff5aa
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Eigen Reflection Maps proof a091c329dbe0: P2 M Ground Theory Heights  Heights Finite Covolume Eigen Reflection Maps proof a091c329dbe0
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Eigen Reflection Maps proof a091c329dbe0 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Eigen Reflection Maps proof a091c329dbe0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PEigenReflectionMaps.lean#L37-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PEigenReflectionMaps.lean#L37-L76

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
variable (ι)

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_EigenReflectionMaps_proof_a091c329dbe0 (h₁ : EigenReflection.Statement ι)
    (h₂ : EigenspacesOrthogonal.Statement ι) : EigenReflectionMaps.Statement ι := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«EigenReflectionMaps».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_EigenReflectionMaps_proof_a091c329dbe0
