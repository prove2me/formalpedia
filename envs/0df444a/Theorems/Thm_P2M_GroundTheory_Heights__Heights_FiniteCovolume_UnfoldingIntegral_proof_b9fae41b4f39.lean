-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldingIntegral_proof_b9fae41b4f39
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldingIntegral_proof_b9fae41b4f39
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:07.101591+00:00
-- url     : https://prove2.me/theorems/67d3680e-a8b6-57b2-827b-d704fd89ce08
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Unfolding Integral proof b9fae41b4f39: P2 M Ground Theory Heights  Heights Finite Covolume Unfolding Integral proof b9fae41b4f39
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Unfolding Integral proof b9fae41b4f39 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Unfolding Integral proof b9fae41b4f39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingIntegral.lean#L44-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingIntegral.lean#L44-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldingTorus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVecAtNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldingIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchLatticeDiscrete_proof_fb679be34432
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_VecAtNeZero_proof_8dea7b49204d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldingIntegral_proof_b9fae41b4f39 (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : UnfoldingTorus.Statement h v)
    (h₂ : TorusIntegralHomogeneous.Statement (InfinitePlace E))
    (h₃ : DiscreteFundamentalDomain.Statement (archUnitary h v)) :
    UnfoldingIntegral.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«UnfoldingIntegral».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldingIntegral_proof_b9fae41b4f39
