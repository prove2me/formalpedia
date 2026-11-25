-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_exists_poly_of_linEval_eq_zero_7478f6dc9d62
-- name    : P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_exists_poly_of_linEval_eq_zero_7478f6dc9d62
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:55.414991+00:00
-- url     : https://prove2.me/theorems/dca16f00-1eb3-541f-9c5c-bc4475fedd21
-- title:
--   P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff exists poly of lin Eval eq zero 7478f6dc9d62: P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff exists poly of lin Eval eq z
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff exists poly of lin Eval eq zero 7478f6dc9d62 construction uses the P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff exists poly of lin Eval eq zero 7478f6dc9d62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightDiffLemmas.lean#L33-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightDiffLemmas.lean#L33-L63

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

theorem P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_exists_poly_of_linEval_eq_zero_7478f6dc9d62 (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection J A) (u : Fin n → ℂ) (hu : linForm u ∉ J) :
    ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧
      ∀ x ∈ zeroSet J, linEval u x = 0 → eval (A *ᵥ x) P = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«LelongWeightDiff».«exists_poly_of_linEval_eq_zero» := P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_exists_poly_of_linEval_eq_zero_7478f6dc9d62
