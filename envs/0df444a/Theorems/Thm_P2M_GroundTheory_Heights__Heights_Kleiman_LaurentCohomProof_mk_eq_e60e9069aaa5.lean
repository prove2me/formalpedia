-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mk_eq_e60e9069aaa5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mk_eq_e60e9069aaa5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:17.21626+00:00
-- url     : https://prove2.me/theorems/e7e328d6-6f90-48cd-88a5-ba8d99b4a0bb
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof mk eq e60e9069aaa5: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof mk eq e60e9069aaa5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof mk eq e60e9069aaa5 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof mk eq e60e9069aaa5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L209-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L209-L214

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mk_eq_e60e9069aaa5 {c : ℤ} {i : ℕ} {z w : Cech.Cochain (G S N) i}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i)
    (hw : w ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i)
    (h : z - w ∈ Cech.bdryDeg (G S N) (laurentDeg S N c) (ρ S N) i) :
    (Submodule.Quotient.mk ⟨z, hz⟩ : laurentCohom S N i c) = Submodule.Quotient.mk ⟨w, hw⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«mk_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mk_eq_e60e9069aaa5
