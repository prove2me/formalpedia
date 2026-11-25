-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_conj_mem_integralClosure_3d6754791d38
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_conj_mem_integralClosure_3d6754791d38
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:23.833268+00:00
-- url     : https://prove2.me/theorems/4ac408c1-b4ab-486a-a80f-a645c9d55e1f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent conj mem integral Closure 3d6754791d38: P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent conj mem integral
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent conj mem integral Closure 3d6754791d38 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent conj mem integral Closure 3d6754791d38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRationalUnipotent.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRationalUnipotent.lean#L98-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRationalUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.RationalUnipotent
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_conj_mem_integralClosure_3d6754791d38 {c : E} (hc : c ∈ integralClosure ℤ E) :
    conj F E c ∈ integralClosure ℤ E := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«RationalUnipotent».«conj_mem_integralClosure» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_conj_mem_integralClosure_3d6754791d38
