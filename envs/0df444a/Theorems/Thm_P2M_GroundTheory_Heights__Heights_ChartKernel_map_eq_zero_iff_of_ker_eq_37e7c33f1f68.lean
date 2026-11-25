-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_map_eq_zero_iff_of_ker_eq_37e7c33f1f68
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_map_eq_zero_iff_of_ker_eq_37e7c33f1f68
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:56.549902+00:00
-- url     : https://prove2.me/theorems/3b1cb10f-f002-4c95-a3bf-8512d328b954
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel map eq zero iff of ker eq 37e7c33f1f68: P2 M Ground Theory Heights  Heights Chart Kernel map eq zero iff of ker eq 37e7c33f1f68
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel map eq zero iff of ker eq 37e7c33f1f68 construction uses the P2 M Ground Theory Heights  Heights Chart Kernel map eq zero iff of ker eq 37e7c33f1f68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L24-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartKernel

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_map_eq_zero_iff_of_ker_eq_37e7c33f1f68 {A B B' σ : Type*} [CommRing A] [CommRing B] [CommRing B']
    {f : A →+* B} {f' : A →+* B'} (h : RingHom.ker f = RingHom.ker f') (x : MvPolynomial σ A) :
    map f x = 0 ↔ map f' x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«map_eq_zero_iff_of_ker_eq» := P2M_GroundTheory_Heights__Heights_ChartKernel_map_eq_zero_iff_of_ker_eq_37e7c33f1f68
