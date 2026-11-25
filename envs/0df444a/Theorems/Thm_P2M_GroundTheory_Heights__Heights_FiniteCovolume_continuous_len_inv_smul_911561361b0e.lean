-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_len_inv_smul_911561361b0e
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_len_inv_smul_911561361b0e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:39:15.369852+00:00
-- url     : https://prove2.me/theorems/54ab8e74-039c-5fa2-b19c-45f40a6d0e59
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume continuous len inv smul 911561361b0e: P2 M Ground Theory Heights  Heights Finite Covolume continuous len inv smul 911561361b0e
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume continuous len inv smul 911561361b0e construction uses the P2 M Ground Theory Heights  Heights Finite Covolume continuous len inv smul 911561361b0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L49-L57

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_len_inv_smul_911561361b0e {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) : Continuous fun g : archUnitary h v => M.len (g⁻¹ • y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«continuous_len_inv_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_len_inv_smul_911561361b0e
