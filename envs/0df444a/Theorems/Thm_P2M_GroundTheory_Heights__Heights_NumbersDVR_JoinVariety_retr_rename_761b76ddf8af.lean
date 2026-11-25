-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVariety_retr_rename_761b76ddf8af
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVariety_retr_rename_761b76ddf8af
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:09:51.39166+00:00
-- url     : https://prove2.me/theorems/761865ae-ff45-45ef-bfac-21ff588ade73
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Variety retr rename 761b76ddf8af: P2 M Ground Theory Heights  Heights Numbers DVR Join Variety retr rename 761b76ddf8af
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Variety retr rename 761b76ddf8af construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Variety retr rename 761b76ddf8af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinVariety.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinVariety.lean#L42-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinVariety
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinVariety
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
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinVariety
variable {K : Type} {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVariety_retr_rename_761b76ddf8af (F : Type) [Field F] (p : MvPolynomial (Σ k, ι k) F) :
    retr F (rename (liftVar (ι := ι) ptIdx) p) = p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVariety».«retr_rename» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVariety_retr_rename_761b76ddf8af
