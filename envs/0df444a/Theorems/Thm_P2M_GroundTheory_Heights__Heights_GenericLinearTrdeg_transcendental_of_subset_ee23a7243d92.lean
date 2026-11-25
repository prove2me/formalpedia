-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_transcendental_of_subset_ee23a7243d92
-- name    : P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_transcendental_of_subset_ee23a7243d92
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:56.218871+00:00
-- url     : https://prove2.me/theorems/2b62725d-d2d6-53c1-b0ce-82659c100f0d
-- title:
--   P2 M Ground Theory Heights  Heights Generic Linear Trdeg transcendental of subset ee23a7243d92: P2 M Ground Theory Heights  Heights Generic Linear Trdeg transcendental of subset ee23a7243d92
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Linear Trdeg transcendental of subset ee23a7243d92 construction uses the P2 M Ground Theory Heights  Heights Generic Linear Trdeg transcendental of subset ee23a7243d92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PGenericLinearTrdeg.lean#L96-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PGenericLinearTrdeg.lean#L96-L111

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

theorem P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_transcendental_of_subset_ee23a7243d92 {A R₁ R₂ : Type*} [CommRing A] [CommRing R₁] [CommRing R₂]
    [Algebra R₁ A] [Algebra R₂ A] (S₁ : Subalgebra R₁ A) (S₂ : Subalgebra R₂ A)
    (h : (S₁ : Set A) ⊆ S₂) {x : A} (hx : Transcendental S₂ x) : Transcendental S₁ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericLinearTrdeg».«transcendental_of_subset» := P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_transcendental_of_subset_ee23a7243d92
