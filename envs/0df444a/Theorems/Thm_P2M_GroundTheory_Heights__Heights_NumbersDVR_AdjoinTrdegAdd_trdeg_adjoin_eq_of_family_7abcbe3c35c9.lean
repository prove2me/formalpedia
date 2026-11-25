-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AdjoinTrdegAdd_trdeg_adjoin_eq_of_family_7abcbe3c35c9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_AdjoinTrdegAdd_trdeg_adjoin_eq_of_family_7abcbe3c35c9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:22.086445+00:00
-- url     : https://prove2.me/theorems/83fe9ba1-a3bb-4b1a-b0ff-1c058934baa8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Adjoin Trdeg Add trdeg adjoin eq of family 7abcbe3c35c9: P2 M Ground Theory Heights  Heights Numbers DVR Adjoin Trdeg Add trdeg adjoin eq of family 7abc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Adjoin Trdeg Add trdeg adjoin eq of family 7abcbe3c35c9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Adjoin Trdeg Add trdeg adjoin eq of family 7abcbe3c35c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PAdjoinTrdegAdd.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PAdjoinTrdegAdd.lean#L11-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsAdjoinTrdegAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PAdjoinTrdegAdd
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
open Algebra Cardinal Set
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_AdjoinTrdegAdd_trdeg_adjoin_eq_of_family_7abcbe3c35c9 {R L κ : Type} [CommRing R] [CommRing L] [IsDomain L]
    [Algebra R L] (u : Set L) (w : κ → L) (hwu : range w ⊆ u) (hw : AlgebraicIndependent R w)
    (halg : ∀ a ∈ u, IsAlgebraic (adjoin R (range w)) a) :
    trdeg R (adjoin R u) = #κ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«AdjoinTrdegAdd».«trdeg_adjoin_eq_of_family» := P2M_GroundTheory_Heights__Heights_NumbersDVR_AdjoinTrdegAdd_trdeg_adjoin_eq_of_family_7abcbe3c35c9
