-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_one_not_mem_idealMod_1352903a0e1d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_one_not_mem_idealMod_1352903a0e1d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:40:40.260831+00:00
-- url     : https://prove2.me/theorems/013fe86d-a28a-54fa-aa2e-94d21e38e807
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term one not mem ideal Mod 1352903a0e1d: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term one not mem ideal Mod 135290
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term one not mem ideal Mod 1352903a0e1d construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term one not mem ideal Mod 1352903a0e1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L70-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L70-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm
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
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {pp : Ideal (Poly k N)}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_one_not_mem_idealMod_1352903a0e1d (hW : pp.IsPrime) (hle : primeOf (S := k) x ≤ pp) {I : Chart x}
    (hI : ∀ i ∈ I.1, (X i : Poly k N) ∉ pp) : (1 : Ω) ∉ idealMod pp I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Term».«one_not_mem_idealMod» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_one_not_mem_idealMod_1352903a0e1d
