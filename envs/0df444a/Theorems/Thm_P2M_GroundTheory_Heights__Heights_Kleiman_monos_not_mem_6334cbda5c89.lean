-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_not_mem_6334cbda5c89
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_monos_not_mem_6334cbda5c89
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:21:29.792119+00:00
-- url     : https://prove2.me/theorems/0c0dd36a-45a6-4334-ab99-c33eeec7144d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman monos not mem 6334cbda5c89: P2 M Ground Theory Heights  Heights Kleiman monos not mem 6334cbda5c89
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman monos not mem 6334cbda5c89 construction uses the P2 M Ground Theory Heights  Heights Kleiman monos not mem 6334cbda5c89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L130-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L130-L137

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_monos_not_mem_6334cbda5c89 {pp : Ideal (Poly S N)} [hp : pp.IsPrime] {I : Finset (Fin (N + 1))}
    (hI : ∀ i ∈ I, (X i : Poly S N) ∉ pp) {s : Poly S N} (hs : s ∈ monos I) : s ∉ pp := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«monos_not_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_monos_not_mem_6334cbda5c89
