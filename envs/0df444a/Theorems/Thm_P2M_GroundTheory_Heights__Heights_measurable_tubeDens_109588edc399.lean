-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurable_tubeDens_109588edc399
-- name    : P2M_GroundTheory_Heights__Heights_measurable_tubeDens_109588edc399
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:01.916869+00:00
-- url     : https://prove2.me/theorems/c250bf69-5623-4e5e-bfa2-ee028bb4eb9e
-- title:
--   P2 M Ground Theory Heights  Heights measurable tube Dens 109588edc399: P2 M Ground Theory Heights  Heights measurable tube Dens 109588edc399
-- statement:
--   The P2 M Ground Theory Heights  Heights measurable tube Dens 109588edc399 construction uses the P2 M Ground Theory Heights  Heights measurable tube Dens 109588edc399 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffTube.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffTube.lean#L19-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffTube
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeEuclMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffTube
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
open MvPolynomial MeasureTheory Filter Matrix ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_measurable_tubeDens_109588edc399 {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (tubeDens J A P R φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«measurable_tubeDens» := P2M_GroundTheory_Heights__Heights_measurable_tubeDens_109588edc399
