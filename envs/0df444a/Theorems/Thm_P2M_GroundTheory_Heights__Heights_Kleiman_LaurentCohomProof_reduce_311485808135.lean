-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_reduce_311485808135
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_reduce_311485808135
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:02.004569+00:00
-- url     : https://prove2.me/theorems/48441a30-b5c2-4e36-bf34-b0472e890553
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof reduce 311485808135: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof reduce 311485808135
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof reduce 311485808135 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof reduce 311485808135 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L174-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L174-L207

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_reduce_311485808135 (hC : Cech.Cone.Statement.{u, u}) {c : ℤ} {i : ℕ} {z : Cech.Cochain (G S N) i}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i) :
    ∃ w ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i,
      (∀ I, w I ∈ Finsupp.supported S S (bnd c)) ∧
      z - w ∈ Cech.bdryDeg (G S N) (laurentDeg S N c) (ρ S N) i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«reduce» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_reduce_311485808135
