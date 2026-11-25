-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_re_complexLinearCoeffs_dot_68aaf7064e75
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_re_complexLinearCoeffs_dot_68aaf7064e75
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:20:06.766909+00:00
-- url     : https://prove2.me/theorems/84a045f9-9a4f-588d-96df-0713d68bf74b
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel re complex Linear Coeffs dot 68aaf7064e75: P2 M Ground Theory Heights  Heights Hilbert Samuel re complex Linear Coeffs dot 68aaf7064e75
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel re complex Linear Coeffs dot 68aaf7064e75 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel re complex Linear Coeffs dot 68aaf7064e75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComplexTaylorTwo.lean#L73-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComplexTaylorTwo.lean#L73-L84

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_re_complexLinearCoeffs_dot_68aaf7064e75 {D : ℕ} (L : (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (complexLinearCoeffs L ⬝ᵥ z).re = L z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«re_complexLinearCoeffs_dot» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_re_complexLinearCoeffs_dot_68aaf7064e75
