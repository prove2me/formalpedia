-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_conj_mem_integralClosure_f3da3bddeddb
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_conj_mem_integralClosure_f3da3bddeddb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:40:14.357233+00:00
-- url     : https://prove2.me/theorems/8f64520b-e5fb-4c4e-b785-6107e4b0a665
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling conj mem integral Closure f3da3bddeddb: P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling conj mem integral Cl
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling conj mem integral Closure f3da3bddeddb construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling conj mem integral Closure f3da3bddeddb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L103-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIsotropicScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_conj_mem_integralClosure_f3da3bddeddb {z : E}
    (hz : z ∈ integralClosure ℤ E) : conj F E z ∈ integralClosure ℤ E := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«IsotropicScaling».«conj_mem_integralClosure» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_conj_mem_integralClosure_f3da3bddeddb
