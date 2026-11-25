-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ScalingLaw_proof_08e97b3dc7f3
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ScalingLaw_proof_08e97b3dc7f3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:24:01.287059+00:00
-- url     : https://prove2.me/theorems/f99501ff-1cb8-5b5a-8762-a2013d7937b8
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Scaling Law proof 08e97b3dc7f3: P2 M Ground Theory Heights  Heights Finite Covolume Scaling Law proof 08e97b3dc7f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Scaling Law proof 08e97b3dc7f3 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Scaling Law proof 08e97b3dc7f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L113-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L113-L222

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ScalingLaw_proof_08e97b3dc7f3 (h : HermitianForm F E W) (v : Basis ι E W) [FiniteDimensional E W]
    (h₁ : UnfoldingIntegral.Statement h v) (h₂ : VectorOrbitsFinite.Statement h)
    (h₃ : UnfoldOrbit.Statement (archUnitary h v))
    (h₄ : DiscreteFundamentalDomain.Statement (archUnitary h v))
    (h₅ : ArchLatticeDiscrete.Statement h v) : ScalingLaw.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ScalingLaw».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ScalingLaw_proof_08e97b3dc7f3
