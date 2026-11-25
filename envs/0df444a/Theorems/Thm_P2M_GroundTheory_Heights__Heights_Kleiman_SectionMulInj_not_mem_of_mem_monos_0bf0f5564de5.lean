-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_not_mem_of_mem_monos_0bf0f5564de5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_not_mem_of_mem_monos_0bf0f5564de5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:38.710124+00:00
-- url     : https://prove2.me/theorems/2db3a11d-38d0-5c9d-bbdb-bffc76738d1d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj not mem of mem monos 0bf0f5564de5: P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj not mem of mem monos 0bf0f5564de5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj not mem of mem monos 0bf0f5564de5 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj not mem of mem monos 0bf0f5564de5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionMulInj.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionMulInj.lean#L42-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionMulInjSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionMulInj
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
open GroundTheory.Heights₂.Heights.Kleiman.SectionMulInj
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
omit [Algebra S Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_not_mem_of_mem_monos_0bf0f5564de5 {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) {I : Chart x}
    (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) {m : Poly S N} (hm : m ∈ monos I.1) : m ∉ pp := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionMulInj».«not_mem_of_mem_monos» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_not_mem_of_mem_monos_0bf0f5564de5
