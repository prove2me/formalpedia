-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_measurable_chartDens_039b8fbc9b8f
-- name    : P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_measurable_chartDens_039b8fbc9b8f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:40:58.998393+00:00
-- url     : https://prove2.me/theorems/5ebe0fa8-5124-4a21-b4c9-b759f5a47aba
-- title:
--   P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff measurable chart Dens 039b8fbc9b8f: P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff measurable chart Dens 039b8fbc9b8f
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff measurable chart Dens 039b8fbc9b8f construction uses the P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff measurable chart Dens 039b8fbc9b8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightDiffLemmas.lean#L65-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightDiffLemmas.lean#L65-L74

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

theorem P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_measurable_chartDens_039b8fbc9b8f {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {f : (Fin n → ℂ) → ℝ} {ψ : Fin d → (Fin n → ℂ) → ℝ} (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hA : IsFiniteProjection J A)
    (hf : ContinuousOn f (zeroSet J)) (hψ : ∀ i, SmoothNear (zeroSet J) (ψ i)) :
    Measurable (chartDens J A f ψ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«LelongWeightDiff».«measurable_chartDens» := P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_measurable_chartDens_039b8fbc9b8f
