-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldingTorus_proof_c2bfd1b3fbdd
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldingTorus_proof_c2bfd1b3fbdd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:06:58.531794+00:00
-- url     : https://prove2.me/theorems/f2db436f-5a52-5f8c-a7b2-85e975def27f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Unfolding Torus proof c2bfd1b3fbdd: P2 M Ground Theory Heights  Heights Finite Covolume Unfolding Torus proof c2bfd1b3fbdd
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Unfolding Torus proof c2bfd1b3fbdd construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Unfolding Torus proof c2bfd1b3fbdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingTorus.lean#L70-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingTorus.lean#L70-L138

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldingTorus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldAlongSubgroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHaarParabolicCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerCovolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldingTorus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchLatticeDiscrete_proof_fb679be34432
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ScalingLaw_proof_08e97b3dc7f3

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
open scoped ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldingTorus_proof_c2bfd1b3fbdd (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ∀ M : Majorant h v,
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (h₂ : HaarParabolicCoordinates.Statement h v) (h₃ : StabilizerCovolumeFinite.Statement h v) :
    UnfoldingTorus.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«UnfoldingTorus».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldingTorus_proof_c2bfd1b3fbdd
