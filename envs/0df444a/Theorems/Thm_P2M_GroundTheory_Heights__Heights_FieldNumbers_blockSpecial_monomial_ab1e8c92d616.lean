-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_blockSpecial_monomial_ab1e8c92d616
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_blockSpecial_monomial_ab1e8c92d616
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:51:56.375834+00:00
-- url     : https://prove2.me/theorems/bfd2fe2d-1736-5c31-a862-dedb1cc8eed9
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers block Special monomial ab1e8c92d616: P2 M Ground Theory Heights  Heights Field Numbers block Special monomial ab1e8c92d616
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers block Special monomial ab1e8c92d616 construction uses the P2 M Ground Theory Heights  Heights Field Numbers block Special monomial ab1e8c92d616 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PValuativeCentre.lean#L22-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PValuativeCentre.lean#L22-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsValuativeCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartDehomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PValuativeCentre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
  {κ : Type*} [CommRing κ]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_blockSpecial_monomial_ab1e8c92d616 (ρ : MRing ι F →+* κ) (d : (Σ k, ι k) →₀ ℕ) (a : F) :
    blockSpecial ρ (monomial d a) = C (ρ (monomial d a)) *
      monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d)) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«blockSpecial_monomial» := P2M_GroundTheory_Heights__Heights_FieldNumbers_blockSpecial_monomial_ab1e8c92d616
