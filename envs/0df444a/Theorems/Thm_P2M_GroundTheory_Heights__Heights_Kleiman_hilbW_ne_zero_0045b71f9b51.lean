-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_hilbW_ne_zero_0045b71f9b51
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_hilbW_ne_zero_0045b71f9b51
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:21.035921+00:00
-- url     : https://prove2.me/theorems/07eb70a4-f87e-5062-867d-236d18ea2880
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman hilb W ne zero 0045b71f9b51: P2 M Ground Theory Heights  Heights Kleiman hilb W ne zero 0045b71f9b51
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman hilb W ne zero 0045b71f9b51 construction uses the P2 M Ground Theory Heights  Heights Kleiman hilb W ne zero 0045b71f9b51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropHilbW.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropHilbW.lean#L27-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropHilbWSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedSectionsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedNumbersSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechH0SectionsHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumPointSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropHilbW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_hilbW_ne_zero_0045b71f9b51 {x : Fin (N + 1) → Ω} {pp : Ideal (Poly S N)} {e : ℕ} (h : IsSubvar x pp e) :
    x ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«hilbW_ne_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_hilbW_ne_zero_0045b71f9b51
