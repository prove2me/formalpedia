-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_freeBasis_mem_820eb7053f2b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_freeBasis_mem_820eb7053f2b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:30:52.07242+00:00
-- url     : https://prove2.me/theorems/146ebeed-50f4-4a7e-89ba-77fe243884db
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graded Pres free Basis mem 820eb7053f2b: P2 M Ground Theory Heights  Heights Kleiman Graded Pres free Basis mem 820eb7053f2b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graded Pres free Basis mem 820eb7053f2b construction uses the P2 M Ground Theory Heights  Heights Kleiman Graded Pres free Basis mem 820eb7053f2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGradedPres.lean#L138-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGradedPres.lean#L138-L149

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGradedPres
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
open GroundTheory.Heights₂.Heights.Kleiman.GradedPres
variable {S : Type u} [CommRing S] {N : ℕ}
variable {r : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_freeBasis_mem_820eb7053f2b (d : Fin r → ℤ) (j : Fin r) :
    freeBasis.{u, v} S N r j ∈ (freeGraded.{u, v} N d).piece (d j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GradedPres».«freeBasis_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_freeBasis_mem_820eb7053f2b
