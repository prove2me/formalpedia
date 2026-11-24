-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_mem_w_99de7a96f87b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_mem_w_99de7a96f87b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:21.936813+00:00
-- url     : https://prove2.me/theorems/9103a44c-798c-4bd4-85e6-1a6dd95b023a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part mem w 99de7a96f87b: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part mem w 99de7a96f87b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part mem w 99de7a96f87b construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part mem w 99de7a96f87b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L49-L56

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_mem_w_99de7a96f87b {c : ℤ} {J : Finset (Fin (N + 1))} {I : StdCell N} {f : Laurent S N}
    (hf : f ∈ laurentDeg S N c I) : part S J f ∈ wPart S N c J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«part_mem_w» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_mem_w_99de7a96f87b
