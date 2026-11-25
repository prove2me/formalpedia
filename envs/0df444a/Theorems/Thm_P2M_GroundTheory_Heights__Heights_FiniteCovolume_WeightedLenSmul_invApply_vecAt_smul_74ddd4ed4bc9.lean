-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_invApply_vecAt_smul_74ddd4ed4bc9
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_invApply_vecAt_smul_74ddd4ed4bc9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:40:23.555307+00:00
-- url     : https://prove2.me/theorems/738ca3c9-2d7b-49f3-afe3-395700d2d812
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul inv Apply vec At smul 74ddd4ed4bc9: P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul inv Apply vec At smul 74
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul inv Apply vec At smul 74ddd4ed4bc9 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul inv Apply vec At smul 74ddd4ed4bc9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWeightedLenSmul.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWeightedLenSmul.lean#L23-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWeightedLenSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [NumberField E] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_invApply_vecAt_smul_74ddd4ed4bc9 {h : HermitianForm F E W} {v : Basis ι E W}
    (g : archUnitary h v) (a : E) (x : W) (w : InfinitePlace E) :
    invApply g (vecAt v (a • x)) w = w.embedding a • invApply g (vecAt v x) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«WeightedLenSmul».«invApply_vecAt_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_invApply_vecAt_smul_74ddd4ed4bc9
