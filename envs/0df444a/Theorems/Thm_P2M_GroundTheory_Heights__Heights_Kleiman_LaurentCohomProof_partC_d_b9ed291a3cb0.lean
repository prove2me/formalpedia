-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_d_b9ed291a3cb0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_d_b9ed291a3cb0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:20.257212+00:00
-- url     : https://prove2.me/theorems/d00c9c43-9373-4ca4-b754-04fe352d3628
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C d b9ed291a3cb0: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C d b9ed291a3cb0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C d b9ed291a3cb0 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part C d b9ed291a3cb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L100-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L100-L102

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_d_b9ed291a3cb0 (J : Finset (Fin (N + 1))) (i : ℕ) (z : Cech.Cochain (G S N) i) :
    Cech.d (G S N) (ρ S N) i (partC S J i z) = partC S J (i + 1) (Cech.d (G S N) (ρ S N) i z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«partC_d» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_d_b9ed291a3cb0
