-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_re_dot_complexQuadMatrix_d68800a2e786
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_re_dot_complexQuadMatrix_d68800a2e786
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:53.065943+00:00
-- url     : https://prove2.me/theorems/bc9e251e-d2a5-4531-a3aa-4fafe8649adc
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel re dot complex Quad Matrix d68800a2e786: P2 M Ground Theory Heights  Heights Hilbert Samuel re dot complex Quad Matrix d68800a2e786
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel re dot complex Quad Matrix d68800a2e786 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel re dot complex Quad Matrix d68800a2e786 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComplexTaylorTwo.lean#L94-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComplexTaylorTwo.lean#L94-L130

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexTaylor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComplexTaylorTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix Metric
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_re_dot_complexQuadMatrix_d68800a2e786 {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
    (z : Fin D → ℂ) :
    (z ⬝ᵥ (complexQuadMatrix H *ᵥ z)).re = (H z z - H (Complex.I • z) (Complex.I • z)) / 4 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«re_dot_complexQuadMatrix» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_re_dot_complexQuadMatrix_d68800a2e786
