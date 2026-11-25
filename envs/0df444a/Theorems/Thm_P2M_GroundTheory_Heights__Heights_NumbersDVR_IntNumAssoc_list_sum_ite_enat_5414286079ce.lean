-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumAssoc_list_sum_ite_enat_5414286079ce
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumAssoc_list_sum_ite_enat_5414286079ce
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:02.189634+00:00
-- url     : https://prove2.me/theorems/05341e67-ecc2-4780-925a-4765a3cced26
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Assoc list sum ite enat 5414286079ce: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Assoc list sum ite enat 5414286079ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Assoc list sum ite enat 5414286079ce construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Assoc list sum ite enat 5414286079ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumAssoc.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumAssoc.lean#L18-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumAssoc
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumAssoc_list_sum_ite_enat_5414286079ce {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P] :
    (l.map fun a => if P a then (1 : ℕ∞) else 0).sum =
      ((l.map fun a => if P a then (1 : ℕ) else 0).sum : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumAssoc».«list_sum_ite_enat» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumAssoc_list_sum_ite_enat_5414286079ce
