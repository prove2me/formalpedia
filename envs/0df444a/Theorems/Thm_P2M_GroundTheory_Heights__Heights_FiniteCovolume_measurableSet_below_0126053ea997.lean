-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_below_0126053ea997
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_below_0126053ea997
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:58:54.941527+00:00
-- url     : https://prove2.me/theorems/2f250e02-5090-4344-803b-04bc16dddb34
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume measurable Set below 0126053ea997: P2 M Ground Theory Heights  Heights Finite Covolume measurable Set below 0126053ea997
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume measurable Set below 0126053ea997 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume measurable Set below 0126053ea997 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L63-L66

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_below_0126053ea997 {h : HermitianForm F E W} {v : Basis ι E W}
    (M : Majorant h v) (y : InfinitePlace E → ι → ℂ) (t : ℝ) :
    MeasurableSet {g : archUnitary h v | M.len (g⁻¹ • y) < t} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«measurableSet_below» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_below_0126053ea997
