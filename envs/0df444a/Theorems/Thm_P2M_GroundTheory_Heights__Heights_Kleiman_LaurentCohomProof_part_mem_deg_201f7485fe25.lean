-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_mem_deg_201f7485fe25
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_mem_deg_201f7485fe25
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:26.955256+00:00
-- url     : https://prove2.me/theorems/0eb1d87a-4b22-4123-bd7c-0308a94f4239
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part mem deg 201f7485fe25: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part mem deg 201f7485fe25
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part mem deg 201f7485fe25 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part mem deg 201f7485fe25 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L83-L85

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_mem_deg_201f7485fe25 {c : ℤ} {J : Finset (Fin (N + 1))} {I : StdCell N} {f : Laurent S N}
    (hf : f ∈ laurentDeg S N c I) : part S J f ∈ laurentDeg S N c I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«part_mem_deg» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_mem_deg_201f7485fe25
