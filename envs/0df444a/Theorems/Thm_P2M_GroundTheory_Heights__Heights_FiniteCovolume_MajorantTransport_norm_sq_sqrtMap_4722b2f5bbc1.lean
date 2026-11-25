-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_norm_sq_sqrtMap_4722b2f5bbc1
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_norm_sq_sqrtMap_4722b2f5bbc1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:40:15.907724+00:00
-- url     : https://prove2.me/theorems/ef469dc8-d80e-4d05-9813-84132fdcd80c
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport norm sq sqrt Map 4722b2f5bbc1: P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport norm sq sqrt Map 4722b2f5bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport norm sq sqrt Map 4722b2f5bbc1 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport norm sq sqrt Map 4722b2f5bbc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L67-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StMajorantTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMajorantTransport
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
open scoped MatrixOrder ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
open GroundTheory.Heights₂.Heights.FiniteCovolume.MajorantTransport
omit [IsTotallyComplex E] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_norm_sq_sqrtMap_4722b2f5bbc1 (Q : InfinitePlace E → Matrix ι ι ℂ) (y : InfinitePlace E → ι → ℂ) :
    ‖sqrtMap Q y‖ ^ 2 = ∑ w, (star (y w) ⬝ᵥ (((Q w)ᴴ * Q w) *ᵥ y w)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«MajorantTransport».«norm_sq_sqrtMap» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_norm_sq_sqrtMap_4722b2f5bbc1
