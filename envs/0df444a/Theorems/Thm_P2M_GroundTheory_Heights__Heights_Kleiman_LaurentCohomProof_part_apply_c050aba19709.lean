-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_apply_c050aba19709
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_apply_c050aba19709
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:44.591457+00:00
-- url     : https://prove2.me/theorems/f8547f85-655f-4ec7-bddf-0f3e51662eab
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part apply c050aba19709: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part apply c050aba19709
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part apply c050aba19709 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part apply c050aba19709 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L28-L30

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_apply_c050aba19709 (J : Finset (Fin (N + 1))) (f : Laurent S N) (a : Fin (N + 1) → ℤ) :
    part S J f a = if negSet a = J then f a else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«part_apply» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_apply_c050aba19709
