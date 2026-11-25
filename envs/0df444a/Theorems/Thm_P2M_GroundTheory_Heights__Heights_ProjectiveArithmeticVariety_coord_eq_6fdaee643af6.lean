-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_coord_eq_6fdaee643af6
-- name    : P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_coord_eq_6fdaee643af6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:07.10618+00:00
-- url     : https://prove2.me/theorems/7a48b7f1-29fc-492d-8e71-8f0730a296c6
-- title:
--   P2 M Ground Theory Heights  Heights Projective Arithmetic Variety coord eq 6fdaee643af6: P2 M Ground Theory Heights  Heights Projective Arithmetic Variety coord eq 6fdaee643af6
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Arithmetic Variety coord eq 6fdaee643af6 construction uses the P2 M Ground Theory Heights  Heights Projective Arithmetic Variety coord eq 6fdaee643af6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjArithVar.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjArithVar.lean#L24-L28

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

theorem P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_coord_eq_6fdaee643af6 (m : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (j : Fin (n + 1)) :
    projSpaceCoord K (n + 1) ⟨(), (m, j)⟩ =
      algebraMap K (ProjField K (n + 1)) (integralBasis K m) * xc K n j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectiveArithmeticVariety».«coord_eq» := P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_coord_eq_6fdaee643af6
