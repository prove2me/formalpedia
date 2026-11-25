-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_not_dvd_pderiv_of_degreeOf_pos_961cad1c5a74
-- name    : P2M_GroundTheory_Heights__Heights_not_dvd_pderiv_of_degreeOf_pos_961cad1c5a74
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:13.849795+00:00
-- url     : https://prove2.me/theorems/e03a6928-138c-4e09-92c7-cff542f96876
-- title:
--   P2 M Ground Theory Heights  Heights not dvd pderiv of degree Of pos 961cad1c5a74: P2 M Ground Theory Heights  Heights not dvd pderiv of degree Of pos 961cad1c5a74
-- statement:
--   The P2 M Ground Theory Heights  Heights not dvd pderiv of degree Of pos 961cad1c5a74 construction uses the P2 M Ground Theory Heights  Heights not dvd pderiv of degree Of pos 961cad1c5a74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormBirational.lean#L42-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormBirational.lean#L42-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormBirational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_not_dvd_pderiv_of_degreeOf_pos_961cad1c5a74 {F σ : Type*} [Field F] [CharZero F] {g : MvPolynomial σ F}
    (hg : g ≠ 0) {i : σ} (hi : 0 < degreeOf i g) : ¬ g ∣ pderiv i g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«not_dvd_pderiv_of_degreeOf_pos» := P2M_GroundTheory_Heights__Heights_not_dvd_pderiv_of_degreeOf_pos_961cad1c5a74
