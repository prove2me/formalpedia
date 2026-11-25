-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_of_mem_vecFixGroup_0d425fc8bfb2
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_of_mem_vecFixGroup_0d425fc8bfb2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:37:24.37288+00:00
-- url     : https://prove2.me/theorems/e11d0255-f3ec-458f-8259-79de011ff043
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume inv Apply of mem vec Fix Group 0d425fc8bfb2: P2 M Ground Theory Heights  Heights Finite Covolume inv Apply of mem vec Fix Group 0d425fc8bfb2
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume inv Apply of mem vec Fix Group 0d425fc8bfb2 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume inv Apply of mem vec Fix Group 0d425fc8bfb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingTorus.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingTorus.lean#L30-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldingTorus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldAlongSubgroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHaarParabolicCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerCovolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldingTorus
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
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_of_mem_vecFixGroup_0d425fc8bfb2 {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {x : archUnitary h v} (hx : x ∈ vecFixGroup h v x₀) : invApply x (vecAt v x₀) = vecAt v x₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«invApply_of_mem_vecFixGroup» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_of_mem_vecFixGroup_0d425fc8bfb2
