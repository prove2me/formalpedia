-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_tildeSys_twist_dbe5ec796d37
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_tildeSys_twist_dbe5ec796d37
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:47.333902+00:00
-- url     : https://prove2.me/theorems/a1900b86-5e91-4158-9344-2717ebc26cac
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman coord Graded tilde Sys twist dbe5ec796d37: P2 M Ground Theory Heights  Heights Kleiman coord Graded tilde Sys twist dbe5ec796d37
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman coord Graded tilde Sys twist dbe5ec796d37 construction uses the P2 M Ground Theory Heights  Heights Kleiman coord Graded tilde Sys twist dbe5ec796d37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanish.lean#L38-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanish.lean#L38-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_tildeSys_twist_dbe5ec796d37 (X : SubSystem k x Ω) :
    ((coordGraded k x).tildeSys 0).twist X = X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coordGraded_tildeSys_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_tildeSys_twist_dbe5ec796d37
