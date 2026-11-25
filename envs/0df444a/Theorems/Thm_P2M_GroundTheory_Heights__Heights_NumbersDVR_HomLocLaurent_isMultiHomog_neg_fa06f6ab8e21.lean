-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isMultiHomog_neg_fa06f6ab8e21
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isMultiHomog_neg_fa06f6ab8e21
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:36.080072+00:00
-- url     : https://prove2.me/theorems/5792ed48-92c2-45e9-8f1a-318f89cd319d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent is Multi Homog neg fa06f6ab8e21: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent is Multi Homog neg fa06f6ab8e21
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent is Multi Homog neg fa06f6ab8e21 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent is Multi Homog neg fa06f6ab8e21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L49-L53

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isMultiHomog_neg_fa06f6ab8e21 {f : MRing ι R} {b : K → ℕ} (hf : IsMultiHomog f b) :
    IsMultiHomog (-f) b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocLaurent».«isMultiHomog_neg» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isMultiHomog_neg_fa06f6ab8e21
