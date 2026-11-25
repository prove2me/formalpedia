-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mem_form_fa180a587675
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mem_form_fa180a587675
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:21:10.163913+00:00
-- url     : https://prove2.me/theorems/95898f35-def7-40a2-9f1c-66000377ff4d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ideal Mod mem form fa180a587675: P2 M Ground Theory Heights  Heights Kleiman ideal Mod mem form fa180a587675
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ideal Mod mem form fa180a587675 construction uses the P2 M Ground Theory Heights  Heights Kleiman ideal Mod mem form fa180a587675 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L112-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L112-L128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
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
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mem_form_fa180a587675 (J : Ideal (Poly S N)) (I : Chart x) {a : Ω} (ha : a ∈ idealMod J I) :
    ∃ (g s : Poly S N) (e : ℕ), g ∈ J ∧ s ∈ monos I.1 ∧ g.IsHomogeneous e ∧ s.IsHomogeneous e ∧
      a = aeval x g / aeval x s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«idealMod_mem_form» := P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mem_form_fa180a587675
