-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_archSmul_apply_a816435a31d0
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_archSmul_apply_a816435a31d0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:08.699234+00:00
-- url     : https://prove2.me/theorems/ac0a9d25-fbb9-5c06-bb29-a6f329eaad6e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume arch Smul apply a816435a31d0: P2 M Ground Theory Heights  Heights Finite Covolume arch Smul apply a816435a31d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume arch Smul apply a816435a31d0 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume arch Smul apply a816435a31d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L42-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]
attribute [local instance] archMulAction

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_archSmul_apply_a816435a31d0 {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v)
    (y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    (g • y) w = ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«archSmul_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_archSmul_apply_a816435a31d0
