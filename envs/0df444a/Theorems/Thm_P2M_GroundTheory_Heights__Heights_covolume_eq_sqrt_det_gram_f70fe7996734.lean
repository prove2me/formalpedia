-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_covolume_eq_sqrt_det_gram_f70fe7996734
-- name    : P2M_GroundTheory_Heights__Heights_covolume_eq_sqrt_det_gram_f70fe7996734
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:35.953964+00:00
-- url     : https://prove2.me/theorems/d432d901-c459-42e1-9fb8-36b9b07df4c5
-- title:
--   P2 M Ground Theory Heights  Heights covolume eq sqrt det gram f70fe7996734: P2 M Ground Theory Heights  Heights covolume eq sqrt det gram f70fe7996734
-- statement:
--   The P2 M Ground Theory Heights  Heights covolume eq sqrt det gram f70fe7996734 construction uses the P2 M Ground Theory Heights  Heights covolume eq sqrt det gram f70fe7996734 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CovolumeGram.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CovolumeGram.lean#L7-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Matrix Module

theorem P2M_GroundTheory_Heights__Heights_covolume_eq_sqrt_det_gram_f70fe7996734 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    ZLattice.covolume L = Real.sqrt (gram ℝ fun i ↦ (b i : V)).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«covolume_eq_sqrt_det_gram» := P2M_GroundTheory_Heights__Heights_covolume_eq_sqrt_det_gram_f70fe7996734
