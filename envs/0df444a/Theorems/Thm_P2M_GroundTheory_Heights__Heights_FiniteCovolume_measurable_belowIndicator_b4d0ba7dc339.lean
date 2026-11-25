-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurable_belowIndicator_b4d0ba7dc339
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurable_belowIndicator_b4d0ba7dc339
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:39:45.973085+00:00
-- url     : https://prove2.me/theorems/a6bbaa70-161d-4428-aa17-ae8dbef81c29
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume measurable below Indicator b4d0ba7dc339: P2 M Ground Theory Heights  Heights Finite Covolume measurable below Indicator b4d0ba7dc339
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume measurable below Indicator b4d0ba7dc339 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume measurable below Indicator b4d0ba7dc339 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L68-L71

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurable_belowIndicator_b4d0ba7dc339 {h : HermitianForm F E W} {v : Basis ι E W}
    (M : Majorant h v) (y : InfinitePlace E → ι → ℂ) (t : ℝ) :
    Measurable (belowIndicator M y t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«measurable_belowIndicator» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurable_belowIndicator_b4d0ba7dc339
