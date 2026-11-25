-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_adjoin_subset_797b8e5e09f9
-- name    : P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_adjoin_subset_797b8e5e09f9
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:07.703966+00:00
-- url     : https://prove2.me/theorems/004e921e-af25-48db-9cda-b03a4ed1b55a
-- title:
--   P2 M Ground Theory Heights  Heights Generic Linear Trdeg adjoin subset 797b8e5e09f9: P2 M Ground Theory Heights  Heights Generic Linear Trdeg adjoin subset 797b8e5e09f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Linear Trdeg adjoin subset 797b8e5e09f9 construction uses the P2 M Ground Theory Heights  Heights Generic Linear Trdeg adjoin subset 797b8e5e09f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PGenericLinearTrdeg.lean#L113-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PGenericLinearTrdeg.lean#L113-L121

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PGenericLinearTrdeg
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
open GroundTheory.Heights₂.Heights.GenericLinearTrdeg

theorem P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_adjoin_subset_797b8e5e09f9 {A R : Type*} [CommRing A] [CommRing R] [Algebra R A] (T : Subring A)
    (s : Set A) (h1 : ∀ c : R, algebraMap R A c ∈ T) (h2 : s ⊆ T) :
    (Algebra.adjoin R s : Set A) ⊆ T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericLinearTrdeg».«adjoin_subset» := P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_adjoin_subset_797b8e5e09f9
