-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_aeval_mul_of_isHomogeneous_4651ac7a1fe2
-- name    : P2M_GroundTheory_Heights__Heights_ChartLocDomain_aeval_mul_of_isHomogeneous_4651ac7a1fe2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:58.319805+00:00
-- url     : https://prove2.me/theorems/b2b06ea0-ecfc-43b6-a69f-8a81d86041d1
-- title:
--   P2 M Ground Theory Heights  Heights Chart Loc Domain aeval mul of is Homogeneous 4651ac7a1fe2: P2 M Ground Theory Heights  Heights Chart Loc Domain aeval mul of is Homogeneous 4651ac7a1fe2
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Loc Domain aeval mul of is Homogeneous 4651ac7a1fe2 construction uses the P2 M Ground Theory Heights  Heights Chart Loc Domain aeval mul of is Homogeneous 4651ac7a1fe2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocDomain.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocDomain.lean#L15-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLocDomain
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartLocDomain_aeval_mul_of_isHomogeneous_4651ac7a1fe2 {A : Type*} [CommRing A] [Algebra F A]
    {g : MvPolynomial (Fin n) F} {d : ℕ} (hg : g.IsHomogeneous d) (c : A) (x : Fin n → A) :
    aeval (fun m => c * x m) g = c ^ d * aeval x g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLocDomain».«aeval_mul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_ChartLocDomain_aeval_mul_of_isHomogeneous_4651ac7a1fe2
