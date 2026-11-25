-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_finrank_step_0e1c7e28817d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_finrank_step_0e1c7e28817d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:00.587569+00:00
-- url     : https://prove2.me/theorems/af32ba37-a166-4e6b-9fa1-cb03d415aaa5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Filtration Step Hilb finrank step 0e1c7e28817d: P2 M Ground Theory Heights  Heights Numbers DVR Filtration Step Hilb finrank step 0e1c7e28817d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Filtration Step Hilb finrank step 0e1c7e28817d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Filtration Step Hilb finrank step 0e1c7e28817d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFiltrationStepHilb.lean#L66-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFiltrationStepHilb.lean#L66-L138

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_finrank_step_0e1c7e28817d (L : Ideal (MRing ι F)) (f : MRing ι F) (s : K → ℕ)
    (hL : IsMultiHomogIdeal L) (hf : IsMultiHomog f s) (n : K → ℕ) :
    Module.finrank F (gradedPiece L n) =
      Module.finrank F (gradedPiece (L ⊔ Ideal.span {f}) n) +
        if s ≤ n then Module.finrank F (gradedPiece (L.colon {f}) (n - s)) else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FiltrationStepHilb».«finrank_step» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_finrank_step_0e1c7e28817d
