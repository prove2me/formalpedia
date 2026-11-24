-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_mem_bdry_c8f9b9260b31
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_mem_bdry_c8f9b9260b31
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:26.219215+00:00
-- url     : https://prove2.me/theorems/9ba01441-1688-4b4a-81df-e963e1247622
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C mem bdry c8f9b9260b31: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C mem bdry c8f9b9260b31
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C mem bdry c8f9b9260b31 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C mem bdry c8f9b9260b31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L115-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L115-L126

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_mem_bdry_c8f9b9260b31 (hC : Cech.Cone.Statement.{u, u}) {c : ℤ} {i : ℕ}
    {J : Finset (Fin (N + 1))} (hJ : J ≠ Finset.univ) {z : Cech.Cochain (G S N) (i + 1)}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) (i + 1)) :
    partC S J (i + 1) z ∈ Cech.bdryDeg (G S N) (laurentDeg S N c) (ρ S N) (i + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«partC_mem_bdry» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_mem_bdry_c8f9b9260b31
