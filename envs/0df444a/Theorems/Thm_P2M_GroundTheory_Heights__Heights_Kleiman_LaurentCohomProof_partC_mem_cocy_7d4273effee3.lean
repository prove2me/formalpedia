-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_mem_cocy_7d4273effee3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_mem_cocy_7d4273effee3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:03.866343+00:00
-- url     : https://prove2.me/theorems/d8a508f5-f814-4b4f-a03d-749e398d1dac
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C mem cocy 7d4273effee3: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C mem cocy 7d4273effee3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C mem cocy 7d4273effee3 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C mem cocy 7d4273effee3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L109-L113

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_mem_cocy_7d4273effee3 {c : ℤ} {i : ℕ} (J : Finset (Fin (N + 1))) {z : Cech.Cochain (G S N) i}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i) :
    partC S J i z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«partC_mem_cocy» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_mem_cocy_7d4273effee3
