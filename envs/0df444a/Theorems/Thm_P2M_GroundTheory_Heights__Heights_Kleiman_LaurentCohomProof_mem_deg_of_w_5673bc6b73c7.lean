-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_deg_of_w_5673bc6b73c7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_deg_of_w_5673bc6b73c7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:46.709178+00:00
-- url     : https://prove2.me/theorems/ae4068fd-7f0b-42b0-95a3-42c6a33373c5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof mem deg of w 5673bc6b73c7: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof mem deg of w 5673bc6b73c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof mem deg of w 5673bc6b73c7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof mem deg of w 5673bc6b73c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L72-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L72-L81

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_deg_of_w_5673bc6b73c7 {c : ℤ} {J : Finset (Fin (N + 1))} {I : StdCell N} {y : Laurent S N}
    (hy : y ∈ wPart S N c J) (hJ : ¬ J ⊆ I.1 → y = 0) : y ∈ laurentDeg S N c I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«mem_deg_of_w» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_deg_of_w_5673bc6b73c7
