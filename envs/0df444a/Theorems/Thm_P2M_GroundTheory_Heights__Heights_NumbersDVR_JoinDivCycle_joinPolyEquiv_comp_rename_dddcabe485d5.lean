-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_joinPolyEquiv_comp_rename_dddcabe485d5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_joinPolyEquiv_comp_rename_dddcabe485d5
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:21.936597+00:00
-- url     : https://prove2.me/theorems/4f778894-6283-48d7-ab0b-9b1a4a200e65
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle join Poly Equiv comp rename dddcabe485d5: P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle join Poly Equiv comp rename dddc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle join Poly Equiv comp rename dddcabe485d5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle join Poly Equiv comp rename dddcabe485d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinDivCycle.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinDivCycle.lean#L38-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinDivCycle
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinDivCycle
variable {R : Type} [CommRing R] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_joinPolyEquiv_comp_rename_dddcabe485d5 :
    (joinPolyEquiv (R := R) (ι := ι)).toRingHom.comp (rename (R := R) (liftVar (ι := ι) ptIdx)).toRingHom =
      Polynomial.C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinDivCycle».«joinPolyEquiv_comp_rename» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_joinPolyEquiv_comp_rename_dddcabe485d5
