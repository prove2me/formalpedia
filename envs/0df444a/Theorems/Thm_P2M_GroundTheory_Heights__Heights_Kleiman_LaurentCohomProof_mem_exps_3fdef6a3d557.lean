-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_exps_3fdef6a3d557
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_exps_3fdef6a3d557
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:30.381805+00:00
-- url     : https://prove2.me/theorems/37991921-5925-423a-8d6d-c363b7e4f4a3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof mem exps 3fdef6a3d557: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof mem exps 3fdef6a3d557
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof mem exps 3fdef6a3d557 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof mem exps 3fdef6a3d557 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L44-L47

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_exps_3fdef6a3d557 {c : ℤ} {I : StdCell N} {f : Laurent S N} (hf : f ∈ laurentDeg S N c I)
    {a : Fin (N + 1) → ℤ} (ha : f a ≠ 0) : a ∈ laurentExps N c I.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«mem_exps» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_exps_3fdef6a3d557
