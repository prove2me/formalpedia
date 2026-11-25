-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isMultiHomog_add_6df46c87f520
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isMultiHomog_add_6df46c87f520
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:32:12.132435+00:00
-- url     : https://prove2.me/theorems/8ded4805-5f67-4fa5-95f9-020f43992f3e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent is Multi Homog add 6df46c87f520: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent is Multi Homog add 6df46c87f520
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent is Multi Homog add 6df46c87f520 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent is Multi Homog add 6df46c87f520 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L42-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
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
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
variable (P W : Ideal (MRing ι R)) [P.IsPrime]
variable {P W}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isMultiHomog_add_6df46c87f520 {f g : MRing ι R} {b : K → ℕ} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g b) : IsMultiHomog (f + g) b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocLaurent».«isMultiHomog_add» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isMultiHomog_add_6df46c87f520
