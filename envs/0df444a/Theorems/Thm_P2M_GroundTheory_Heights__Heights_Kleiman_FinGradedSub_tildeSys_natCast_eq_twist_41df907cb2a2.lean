-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_tildeSys_natCast_eq_twist_41df907cb2a2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_tildeSys_natCast_eq_twist_41df907cb2a2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:02:32.907811+00:00
-- url     : https://prove2.me/theorems/65b72815-d2ce-5992-bebc-2113340464f0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub tilde Sys nat Cast eq twist 41df907cb2a2: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub tilde Sys nat Cast eq twist 41df907cb2a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub tilde Sys nat Cast eq twist 41df907cb2a2 construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub tilde Sys nat Cast eq twist 41df907cb2a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleVanish.lean#L20-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleVanish.lean#L20-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleVanish
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_tildeSys_natCast_eq_twist_41df907cb2a2 (M : FinGradedSub (S := S) (x := x) E) (a : ℕ) :
    M.tildeSys (a : ℤ) = (M.tildeSys 0).twist (twistSys S x (a : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«tildeSys_natCast_eq_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_tildeSys_natCast_eq_twist_41df907cb2a2
