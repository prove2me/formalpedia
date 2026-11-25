-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_stabilizer_vecAt_ade5addf10ad
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_stabilizer_vecAt_ade5addf10ad
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:39:26.082421+00:00
-- url     : https://prove2.me/theorems/9f621f63-8858-5c3b-b52f-e0b5c982bc49
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume stabilizer vec At ade5addf10ad: P2 M Ground Theory Heights  Heights Finite Covolume stabilizer vec At ade5addf10ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume stabilizer vec At ade5addf10ad construction uses the P2 M Ground Theory Heights  Heights Finite Covolume stabilizer vec At ade5addf10ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L97-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L97-L111

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
variable [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_stabilizer_vecAt_ade5addf10ad (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W)
    (y : W) : MulAction.stabilizer (archLatticeGroup h v La) (vecAt v y) =
      (vecStabGroup h v La y).subgroupOf (archLatticeGroup h v La) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«stabilizer_vecAt» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_stabilizer_vecAt_ade5addf10ad
