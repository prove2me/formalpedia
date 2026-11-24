-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_eq_zero_5c5c6203c57c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_eq_zero_5c5c6203c57c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:29.990379+00:00
-- url     : https://prove2.me/theorems/e5e28be3-f4c8-4ad5-be7d-296060cd99a0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part eq zero 5c5c6203c57c: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part eq zero 5c5c6203c57c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part eq zero 5c5c6203c57c construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part eq zero 5c5c6203c57c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L58-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L58-L70

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_eq_zero_5c5c6203c57c {c : ℤ} {J : Finset (Fin (N + 1))} {I : StdCell N} {f : Laurent S N}
    (hf : f ∈ laurentDeg S N c I) (hJ : ¬ J ⊆ I.1) : part S J f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«part_eq_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_eq_zero_5c5c6203c57c
