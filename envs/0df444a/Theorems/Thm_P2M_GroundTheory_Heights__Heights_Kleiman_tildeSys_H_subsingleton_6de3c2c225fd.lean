-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tildeSys_H_subsingleton_6de3c2c225fd
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_tildeSys_H_subsingleton_6de3c2c225fd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:13:11.797689+00:00
-- url     : https://prove2.me/theorems/916baf77-d1e2-5f5b-af0d-f3b47425ced7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman tilde Sys H subsingleton 6de3c2c225fd: P2 M Ground Theory Heights  Heights Kleiman tilde Sys H subsingleton 6de3c2c225fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman tilde Sys H subsingleton 6de3c2c225fd construction uses the P2 M Ground Theory Heights  Heights Kleiman tilde Sys H subsingleton 6de3c2c225fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L103-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean#L103-L139

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
variable (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_tildeSys_H_subsingleton_6de3c2c225fd (k : ℕ) (h : Subsingleton (cohom M.coneGradedE (k + 1) c)) :
    Subsingleton ((M.tildeSys c).H (k + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«tildeSys_H_subsingleton» := P2M_GroundTheory_Heights__Heights_Kleiman_tildeSys_H_subsingleton_6de3c2c225fd
