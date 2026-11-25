-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_mul_76e777226916
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_mul_76e777226916
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:37:32.248262+00:00
-- url     : https://prove2.me/theorems/bc9454eb-6279-42e0-b650-20ba9b711f43
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume inv Apply mul 76e777226916: P2 M Ground Theory Heights  Heights Finite Covolume inv Apply mul 76e777226916
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume inv Apply mul 76e777226916 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume inv Apply mul 76e777226916 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingTorus.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingTorus.lean#L22-L26

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_mul_76e777226916 {h : HermitianForm F E W} {v : Basis ι E W} (a b : archUnitary h v)
    (y : InfinitePlace E → ι → ℂ) : invApply (a * b) y = invApply b (invApply a y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«invApply_mul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_mul_76e777226916
