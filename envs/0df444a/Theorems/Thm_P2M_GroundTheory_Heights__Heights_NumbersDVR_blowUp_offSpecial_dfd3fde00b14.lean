-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_offSpecial_dfd3fde00b14
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_offSpecial_dfd3fde00b14
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:16.054804+00:00
-- url     : https://prove2.me/theorems/a723b7e3-6771-4ff3-be02-d41daae58082
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR blow Up off Special dfd3fde00b14: P2 M Ground Theory Heights  Heights Numbers DVR blow Up off Special dfd3fde00b14
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR blow Up off Special dfd3fde00b14 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR blow Up off Special dfd3fde00b14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L141-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L141-L162

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
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
universe u
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
variable {J : Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_offSpecial_dfd3fde00b14 {P : Ideal (MRing ι R)} (hP : P.IsPrime) {s g f m : MRing ι R} (e : K → ℕ)
    (hg : g ∉ P) {W : Ideal (MRing (extIdx ι (BlowUpIdx ι)) R)} (hW : W.IsPrime)
    (hQW : blowUpOf P (blowUpGens s g f m e) ≤ W) (hrel : IsRelevant W) {u₀ v₀ : MRing ι R}
    (hv : liftForm v₀ ∉ W) (h : u₀ * f - v₀ * g ∈ P) :
    ∃ i : ∀ k, ι k, liftForm (powMonomial e i) ∉ W ∧ newVar (some (some i)) ∉ W ∧
      (liftForm m ∉ W → newVar (some none) ∉ W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«blowUp_offSpecial» := P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_offSpecial_dfd3fde00b14
