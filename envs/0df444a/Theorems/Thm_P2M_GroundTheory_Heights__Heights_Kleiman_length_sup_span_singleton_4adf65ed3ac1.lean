-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_length_sup_span_singleton_4adf65ed3ac1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_length_sup_span_singleton_4adf65ed3ac1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:54.192162+00:00
-- url     : https://prove2.me/theorems/f8d6f03e-4094-4577-9b75-df40a7e40427
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman length sup span singleton 4adf65ed3ac1: P2 M Ground Theory Heights  Heights Kleiman length sup span singleton 4adf65ed3ac1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman length sup span singleton 4adf65ed3ac1 construction uses the P2 M Ground Theory Heights  Heights Kleiman length sup span singleton 4adf65ed3ac1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationExists.lean#L24-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationExists.lean#L24-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationExists
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
universe u v w
variable {R : Type*} [CommRing R] {L : Type*} [AddCommGroup L] [Module R L]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_length_sup_span_singleton_4adf65ed3ac1 (A : Submodule R L) (y : L) :
    Module.length R (A ⊔ Submodule.span R {y} : Submodule R L) =
      Module.length R A + Module.length R (R ⧸ colonIdeal A y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«length_sup_span_singleton» := P2M_GroundTheory_Heights__Heights_Kleiman_length_sup_span_singleton_4adf65ed3ac1
