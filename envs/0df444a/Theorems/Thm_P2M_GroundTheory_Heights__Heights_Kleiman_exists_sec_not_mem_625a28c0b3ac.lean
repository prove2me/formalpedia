-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_sec_not_mem_625a28c0b3ac
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_sec_not_mem_625a28c0b3ac
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:21:11.860905+00:00
-- url     : https://prove2.me/theorems/15a86895-2d35-4649-9657-313392e13d2f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists sec not mem 625a28c0b3ac: P2 M Ground Theory Heights  Heights Kleiman exists sec not mem 625a28c0b3ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists sec not mem 625a28c0b3ac construction uses the P2 M Ground Theory Heights  Heights Kleiman exists sec not mem 625a28c0b3ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L139-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L139-L174

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_sec_not_mem_625a28c0b3ac (L : LineBundle S x) (hL : IsVeryAmple L.toSubSystem)
    {pp : Ideal (Poly S N)} {e : ℕ} (hW : IsSubvar x pp e) :
    ∃ s ∈ L.secs, ∃ I, s ∉ (L.twist (idealSys x pp)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_sec_not_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_sec_not_mem_625a28c0b3ac
