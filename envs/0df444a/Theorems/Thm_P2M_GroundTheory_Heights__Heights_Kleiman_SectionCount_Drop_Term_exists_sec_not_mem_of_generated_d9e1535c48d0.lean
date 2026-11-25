-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_sec_not_mem_of_generated_d9e1535c48d0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_sec_not_mem_of_generated_d9e1535c48d0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:26.514533+00:00
-- url     : https://prove2.me/theorems/7cd7c368-26dc-5f01-9a20-5702547355b3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term exists sec not mem of generated d9e1535c48d0: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term exists sec not mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term exists sec not mem of generated d9e1535c48d0 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term exists sec not mem of generated d9e1535c48d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L181-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L181-L199

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_sec_not_mem_of_generated_d9e1535c48d0 (G : SubSystem k x Ω) (hG : G.Generated)
    (hinv : ∀ I, ∃ G' : Submodule (chartRing k x I) Ω, G.sub I * G' = 1) (hW : pp.IsPrime)
    (hle : primeOf (S := k) x ≤ pp) {I : Chart x} (hI : ∀ i ∈ I.1, (X i : Poly k N) ∉ pp) :
    ∃ t ∈ G.secs, t ∉ idealMod pp I * G.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Term».«exists_sec_not_mem_of_generated» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_sec_not_mem_of_generated_d9e1535c48d0
