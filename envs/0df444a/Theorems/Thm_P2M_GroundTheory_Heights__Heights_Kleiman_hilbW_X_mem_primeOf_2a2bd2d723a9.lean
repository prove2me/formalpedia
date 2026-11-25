-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_hilbW_X_mem_primeOf_2a2bd2d723a9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_hilbW_X_mem_primeOf_2a2bd2d723a9
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:08:20.707801+00:00
-- url     : https://prove2.me/theorems/fdaea1d1-7caa-42bc-b1f2-cb276d698b14
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman hilb W X mem prime Of 2a2bd2d723a9: P2 M Ground Theory Heights  Heights Kleiman hilb W X mem prime Of 2a2bd2d723a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman hilb W X mem prime Of 2a2bd2d723a9 construction uses the P2 M Ground Theory Heights  Heights Kleiman hilb W X mem prime Of 2a2bd2d723a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropHilbW.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropHilbW.lean#L23-L25

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_hilbW_X_mem_primeOf_2a2bd2d723a9 (x : Fin (N + 1) → Ω) {i : Fin (N + 1)} (hi : x i = 0) :
    (X i : Poly S N) ∈ primeOf (S := S) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«hilbW_X_mem_primeOf» := P2M_GroundTheory_Heights__Heights_Kleiman_hilbW_X_mem_primeOf_2a2bd2d723a9
