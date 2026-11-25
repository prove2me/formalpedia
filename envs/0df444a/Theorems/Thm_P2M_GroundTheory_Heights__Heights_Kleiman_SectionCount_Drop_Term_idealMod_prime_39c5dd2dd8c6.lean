-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_idealMod_prime_39c5dd2dd8c6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_idealMod_prime_39c5dd2dd8c6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:09:50.713517+00:00
-- url     : https://prove2.me/theorems/8f6c7405-6fd5-4cc3-b8fc-4ac14c163436
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term ideal Mod prime 39c5dd2dd8c6: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term ideal Mod prime 39c5dd2dd8c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term ideal Mod prime 39c5dd2dd8c6 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term ideal Mod prime 39c5dd2dd8c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L84-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L84-L121

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_idealMod_prime_39c5dd2dd8c6 (hW : pp.IsPrime) (hle : primeOf (S := k) x ≤ pp) {I : Chart x}
    (hI : ∀ i ∈ I.1, (X i : Poly k N) ∉ pp) :
    ∀ a ∈ (1 : Submodule (chartRing k x I) Ω), ∀ b ∈ (1 : Submodule (chartRing k x I) Ω),
      a * b ∈ idealMod pp I → a ∈ idealMod pp I ∨ b ∈ idealMod pp I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Term».«idealMod_prime» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_idealMod_prime_39c5dd2dd8c6
