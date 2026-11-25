-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_zero_8c0149e3f6e7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_zero_8c0149e3f6e7
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:29.76615+00:00
-- url     : https://prove2.me/theorems/6030b8ac-d243-4a7e-905d-d5697c4415e8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C zero 8c0149e3f6e7: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C zero 8c0149e3f6e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C zero 8c0149e3f6e7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C zero 8c0149e3f6e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L128-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L128-L136

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_zero_8c0149e3f6e7 (hC : Cech.Cone.Statement.{u, u}) {c : ℤ} {J : Finset (Fin (N + 1))}
    (hJ0 : J ≠ ∅) (hJ : J ≠ Finset.univ) {z : Cech.Cochain (G S N) 0}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) 0) : partC S J 0 z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«partC_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_zero_8c0149e3f6e7
