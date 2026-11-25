-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ringHom_ext_of_not_mem_a2804716ddc4
-- name    : P2M_GroundTheory_Heights__Theta_ringHom_ext_of_not_mem_a2804716ddc4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:54:20.317094+00:00
-- url     : https://prove2.me/theorems/267ec78f-cdd2-4b93-8236-e3f9e55be0b1
-- title:
--   P2 M Ground Theory Heights  Theta ring Hom ext of not mem a2804716ddc4: P2 M Ground Theory Heights  Theta ring Hom ext of not mem a2804716ddc4
-- statement:
--   The P2 M Ground Theory Heights  Theta ring Hom ext of not mem a2804716ddc4 construction uses the P2 M Ground Theory Heights  Theta ring Hom ext of not mem a2804716ddc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L83-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L83-L89

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
variable (F E)
variable {F E}

theorem P2M_GroundTheory_Heights__Theta_ringHom_ext_of_not_mem_a2804716ddc4 {R : Type*} [CommRing R] {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) {φ ψ : E →+* R}
    (hF : ∀ c, φ (algebraMap F E c) = ψ (algebraMap F E c)) (hxe : φ x = ψ x) : φ = ψ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ringHom_ext_of_not_mem» := P2M_GroundTheory_Heights__Theta_ringHom_ext_of_not_mem_a2804716ddc4
