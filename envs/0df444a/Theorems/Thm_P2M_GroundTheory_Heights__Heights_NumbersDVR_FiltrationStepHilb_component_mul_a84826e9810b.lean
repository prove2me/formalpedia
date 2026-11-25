-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_component_mul_a84826e9810b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_component_mul_a84826e9810b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:27.180178+00:00
-- url     : https://prove2.me/theorems/4f59f8a2-1a56-413e-829f-567a50597ce2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Filtration Step Hilb component mul a84826e9810b: P2 M Ground Theory Heights  Heights Numbers DVR Filtration Step Hilb component mul a84826e9810b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Filtration Step Hilb component mul a84826e9810b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Filtration Step Hilb component mul a84826e9810b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFiltrationStepHilb.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFiltrationStepHilb.lean#L39-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.FiltrationStepHilb
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
open Classical

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_component_mul_a84826e9810b {f : MRing ι F} {s : K → ℕ} (hf : IsMultiHomog f s) (c : MRing ι F)
    (n : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) n (f * c) =
      if s ≤ n then f * weightedHomogeneousComponent (blockWeight ι) (n - s) c else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FiltrationStepHilb».«component_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_component_mul_a84826e9810b
