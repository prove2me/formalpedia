-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_mem_idealMod_mul_of_mem_c3f7741d6a4f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_mem_idealMod_mul_of_mem_c3f7741d6a4f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:19.992327+00:00
-- url     : https://prove2.me/theorems/24fab7e2-c921-59ad-80ce-857258664d11
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term mem ideal Mod mul of mem c3f7741d6a4f: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term mem ideal Mod mul of mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term mem ideal Mod mul of mem c3f7741d6a4f construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term mem ideal Mod mul of mem c3f7741d6a4f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L144-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L144-L179

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_mem_idealMod_mul_of_mem_c3f7741d6a4f (L : LineBundle k x) (hW : pp.IsPrime) (hle : primeOf (S := k) x ≤ pp)
    {I K : Chart x} (h : I.1 ⊆ K.1) (hK : ∀ i ∈ K.1, (X i : Poly k N) ∉ pp) {s : Ω}
    (hs : s ∈ L.sub I) (hsK : s ∈ idealMod pp K * L.sub K) : s ∈ idealMod pp I * L.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Term».«mem_idealMod_mul_of_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_mem_idealMod_mul_of_mem_c3f7741d6a4f
