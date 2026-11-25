-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_bnd_finite_04cd16ef5319
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_bnd_finite_04cd16ef5319
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:22.255377+00:00
-- url     : https://prove2.me/theorems/4e0679fa-b107-48a3-8d0b-881ffcefc701
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof bnd finite 04cd16ef5319: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof bnd finite 04cd16ef5319
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof bnd finite 04cd16ef5319 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof bnd finite 04cd16ef5319 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L153-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L153-L172

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
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
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
variable {S : Type u} [CommRing S] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_bnd_finite_04cd16ef5319 (c : ℤ) : (bnd (N := N) c).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«bnd_finite» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_bnd_finite_04cd16ef5319
