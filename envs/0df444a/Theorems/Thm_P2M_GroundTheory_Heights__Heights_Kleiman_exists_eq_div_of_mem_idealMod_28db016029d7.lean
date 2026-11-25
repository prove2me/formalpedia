-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_eq_div_of_mem_idealMod_28db016029d7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_eq_div_of_mem_idealMod_28db016029d7
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:32.187511+00:00
-- url     : https://prove2.me/theorems/43cfe01f-f3b3-5df8-8068-11beb8822a55
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists eq div of mem ideal Mod 28db016029d7: P2 M Ground Theory Heights  Heights Kleiman exists eq div of mem ideal Mod 28db016029d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists eq div of mem ideal Mod 28db016029d7 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists eq div of mem ideal Mod 28db016029d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrQuotTorsionFree.lean#L20-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrQuotTorsionFree.lean#L20-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrQuotTorsionFree
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_eq_div_of_mem_idealMod_28db016029d7 {J : Ideal (Poly S N)} {I : Chart x} {z : Ω}
    (hz : z ∈ idealMod J I) :
    ∃ (f m : Poly S N) (e : ℕ), f ∈ J ∧ m ∈ monos I.1 ∧ f.IsHomogeneous e ∧
      m.IsHomogeneous e ∧ z = aeval x f / aeval x m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_eq_div_of_mem_idealMod» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_eq_div_of_mem_idealMod_28db016029d7
