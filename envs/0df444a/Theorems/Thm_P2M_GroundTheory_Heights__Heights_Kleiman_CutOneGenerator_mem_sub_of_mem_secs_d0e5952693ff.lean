-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_mem_sub_of_mem_secs_d0e5952693ff
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_mem_sub_of_mem_secs_d0e5952693ff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:54:35.490785+00:00
-- url     : https://prove2.me/theorems/da17724b-17f8-4b6d-9081-e364cf388394
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cut One Generator mem sub of mem secs d0e5952693ff: P2 M Ground Theory Heights  Heights Kleiman Cut One Generator mem sub of mem secs d0e5952693ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cut One Generator mem sub of mem secs d0e5952693ff construction uses the P2 M Ground Theory Heights  Heights Kleiman Cut One Generator mem sub of mem secs d0e5952693ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutOneGenerator.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutOneGenerator.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GlobalFunctionsIntegralSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestriction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutOneGenerator
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
open GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_mem_sub_of_mem_secs_d0e5952693ff {S : Type u} [CommRing S] {E : Type w} [Field E] [Algebra S E] {M : ℕ}
    {z : Fin (M + 1) → E} {H : SubSystem S z E} {t : E} (ht : t ∈ H.secs) (I : Chart z) :
    t ∈ H.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CutOneGenerator».«mem_sub_of_mem_secs» := P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_mem_sub_of_mem_secs_d0e5952693ff
