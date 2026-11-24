-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_mulMat_sum_04dda0bf4bd3
-- name    : P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_mulMat_sum_04dda0bf4bd3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:10.939213+00:00
-- url     : https://prove2.me/theorems/92ebf90e-3c73-44b1-8607-62caafb09d31
-- title:
--   P2 M Ground Theory Heights  Heights Projective Points On Plane mul Mat sum 04dda0bf4bd3: P2 M Ground Theory Heights  Heights Projective Points On Plane mul Mat sum 04dda0bf4bd3
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Points On Plane mul Mat sum 04dda0bf4bd3 construction uses the P2 M Ground Theory Heights  Heights Projective Points On Plane mul Mat sum 04dda0bf4bd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L18-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOnPlane
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_mulMat_sum_04dda0bf4bd3 (α : 𝓞 K) (m : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    ∑ n, (mulMat α m n : K) * integralBasis K n = (α : K) * integralBasis K m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectivePointsOnPlane».«mulMat_sum» := P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_mulMat_sum_04dda0bf4bd3
