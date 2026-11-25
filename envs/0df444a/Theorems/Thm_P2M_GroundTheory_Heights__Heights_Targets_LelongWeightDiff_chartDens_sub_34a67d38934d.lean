-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_chartDens_sub_34a67d38934d
-- name    : P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_chartDens_sub_34a67d38934d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:09.033036+00:00
-- url     : https://prove2.me/theorems/79bb5d0f-9034-4b93-8345-d5529e242776
-- title:
--   P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff chart Dens sub 34a67d38934d: P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff chart Dens sub 34a67d38934d
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff chart Dens sub 34a67d38934d construction uses the P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff chart Dens sub 34a67d38934d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightDiffLemmas.lean#L85-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightDiffLemmas.lean#L85-L92

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

theorem P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_chartDens_sub_34a67d38934d {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (f f' : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    chartDens J A f ψ y - chartDens J A f' ψ y = chartDens J A (fun x => f x - f' x) ψ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«LelongWeightDiff».«chartDens_sub» := P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_chartDens_sub_34a67d38934d
