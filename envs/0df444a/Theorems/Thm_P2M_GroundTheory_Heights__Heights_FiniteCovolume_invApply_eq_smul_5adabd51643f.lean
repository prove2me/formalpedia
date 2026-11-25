-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_eq_smul_5adabd51643f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_eq_smul_5adabd51643f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:13:11.213877+00:00
-- url     : https://prove2.me/theorems/1aef369f-fad4-5666-aabd-a36b4213d424
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume inv Apply eq smul 5adabd51643f: P2 M Ground Theory Heights  Heights Finite Covolume inv Apply eq smul 5adabd51643f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume inv Apply eq smul 5adabd51643f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume inv Apply eq smul 5adabd51643f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L46-L47

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_eq_smul_5adabd51643f {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v)
    (y : InfinitePlace E → ι → ℂ) : invApply g y = g⁻¹ • y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«invApply_eq_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_eq_smul_5adabd51643f
