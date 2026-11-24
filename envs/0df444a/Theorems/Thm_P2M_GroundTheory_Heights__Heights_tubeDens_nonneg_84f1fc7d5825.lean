-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_tubeDens_nonneg_84f1fc7d5825
-- name    : P2M_GroundTheory_Heights__Heights_tubeDens_nonneg_84f1fc7d5825
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:56.11141+00:00
-- url     : https://prove2.me/theorems/d24708b2-e7c3-4c5b-90d4-bfef89f0f44e
-- title:
--   P2 M Ground Theory Heights  Heights tube Dens nonneg 84f1fc7d5825: P2 M Ground Theory Heights  Heights tube Dens nonneg 84f1fc7d5825
-- statement:
--   The P2 M Ground Theory Heights  Heights tube Dens nonneg 84f1fc7d5825 construction uses the P2 M Ground Theory Heights  Heights tube Dens nonneg 84f1fc7d5825 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffTube.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffTube.lean#L30-L33

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

theorem P2M_GroundTheory_Heights__Heights_tubeDens_nonneg_84f1fc7d5825 {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin (d + 1)) (Fin n) ℂ) (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin (d + 1) → ℂ) : 0 ≤ tubeDens J A P R φ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«tubeDens_nonneg» := P2M_GroundTheory_Heights__Heights_tubeDens_nonneg_84f1fc7d5825
