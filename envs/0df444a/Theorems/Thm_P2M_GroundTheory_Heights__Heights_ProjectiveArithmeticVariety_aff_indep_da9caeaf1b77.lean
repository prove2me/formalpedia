-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_aff_indep_da9caeaf1b77
-- name    : P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_aff_indep_da9caeaf1b77
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:33.424512+00:00
-- url     : https://prove2.me/theorems/0f35189f-9d10-428e-94fe-55a0de5a68dd
-- title:
--   P2 M Ground Theory Heights  Heights Projective Arithmetic Variety aff indep da9caeaf1b77: P2 M Ground Theory Heights  Heights Projective Arithmetic Variety aff indep da9caeaf1b77
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Arithmetic Variety aff indep da9caeaf1b77 construction uses the P2 M Ground Theory Heights  Heights Projective Arithmetic Variety aff indep da9caeaf1b77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjArithVar.lean#L33-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjArithVar.lean#L33-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjArithVar
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectiveArithmeticVariety
variable (K : Type) [Field K] [NumberField K] (n : ℕ)

theorem P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_aff_indep_da9caeaf1b77 : AlgebraicIndependent ℚ (aff K n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectiveArithmeticVariety».«aff_indep» := P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_aff_indep_da9caeaf1b77
