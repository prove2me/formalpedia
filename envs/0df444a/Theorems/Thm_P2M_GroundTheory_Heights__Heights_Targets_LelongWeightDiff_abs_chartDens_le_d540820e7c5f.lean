-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_abs_chartDens_le_d540820e7c5f
-- name    : P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_abs_chartDens_le_d540820e7c5f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:40:53.928871+00:00
-- url     : https://prove2.me/theorems/248e4df7-9918-4f5f-8a2f-66022e4b2526
-- title:
--   P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff abs chart Dens le d540820e7c5f: P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff abs chart Dens le d540820e7c5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff abs chart Dens le d540820e7c5f construction uses the P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff abs chart Dens le d540820e7c5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightDiffLemmas.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightDiffLemmas.lean#L76-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightDiff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightDiffLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_abs_chartDens_le_d540820e7c5f {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    |chartDens J A f ψ y| ≤ chartAbsDens J A f ψ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«LelongWeightDiff».«abs_chartDens_le» := P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_abs_chartDens_le_d540820e7c5f
