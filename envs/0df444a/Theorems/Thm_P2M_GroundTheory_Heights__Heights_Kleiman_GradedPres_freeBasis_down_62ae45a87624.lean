-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_freeBasis_down_62ae45a87624
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_freeBasis_down_62ae45a87624
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:46.867804+00:00
-- url     : https://prove2.me/theorems/014c3f53-2cb1-4123-8250-557ea210b6e9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graded Pres free Basis down 62ae45a87624: P2 M Ground Theory Heights  Heights Kleiman Graded Pres free Basis down 62ae45a87624
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graded Pres free Basis down 62ae45a87624 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graded Pres free Basis down 62ae45a87624 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGradedPres.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGradedPres.lean#L134-L136

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_freeBasis_down_62ae45a87624 (j : Fin r) : (freeBasis.{u, v} S N r j).down = Pi.single j 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GradedPres».«freeBasis_down» := P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_freeBasis_down_62ae45a87624
