-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecStabGroup_le_vecFixGroup_03fa43eba001
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecStabGroup_le_vecFixGroup_03fa43eba001
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:36:36.737797+00:00
-- url     : https://prove2.me/theorems/a88fc1b1-d3ab-49ef-9394-9c725f54c6fd
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume vec Stab Group le vec Fix Group 03fa43eba001: P2 M Ground Theory Heights  Heights Finite Covolume vec Stab Group le vec Fix Group 03fa43eba001
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume vec Stab Group le vec Fix Group 03fa43eba001 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume vec Stab Group le vec Fix Group 03fa43eba001 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingTorus.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingTorus.lean#L54-L60

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
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecStabGroup_le_vecFixGroup_03fa43eba001 [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
    (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W) (x₀ : W) :
    vecStabGroup h v La x₀ ≤ vecFixGroup h v x₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«vecStabGroup_le_vecFixGroup» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecStabGroup_le_vecFixGroup_03fa43eba001
