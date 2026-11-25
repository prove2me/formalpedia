-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_mem_sup_span_6525c74ca226
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_mem_sup_span_6525c74ca226
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:27.295773+00:00
-- url     : https://prove2.me/theorems/2f843989-166f-41a5-b4da-9d2029219ca5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Filtration Step Hilb mem sup span 6525c74ca226: P2 M Ground Theory Heights  Heights Numbers DVR Filtration Step Hilb mem sup span 6525c74ca226
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Filtration Step Hilb mem sup span 6525c74ca226 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Filtration Step Hilb mem sup span 6525c74ca226 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFiltrationStepHilb.lean#L51-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFiltrationStepHilb.lean#L51-L62

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_mem_sup_span_6525c74ca226 {L : Ideal (MRing ι F)} {f : MRing ι F} {s : K → ℕ}
    (hL : IsMultiHomogIdeal L) (hf : IsMultiHomog f s) {n : K → ℕ} {x : MRing ι F}
    (hx : x ∈ weightedHomogeneousSubmodule F (blockWeight ι) n) (hx' : x ∈ L ⊔ Ideal.span {f}) :
    ∃ c : MRing ι F, x - (if s ≤ n then f * weightedHomogeneousComponent (blockWeight ι) (n - s) c
      else 0) ∈ L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FiltrationStepHilb».«mem_sup_span» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_mem_sup_span_6525c74ca226
