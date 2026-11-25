-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GradedPMod_smul_mem_int_382e083d6e10
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GradedPMod_smul_mem_int_382e083d6e10
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:06.659332+00:00
-- url     : https://prove2.me/theorems/11a2eb3d-306b-5894-af9d-135b7669179a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graded PMod smul mem int 382e083d6e10: P2 M Ground Theory Heights  Heights Kleiman Graded PMod smul mem int 382e083d6e10
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graded PMod smul mem int 382e083d6e10 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graded PMod smul mem int 382e083d6e10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L55-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
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
open MvPolynomial
noncomputable section
universe u v w w'
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
omit [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GradedPMod_smul_mem_int_382e083d6e10 (𝓜 : GradedPMod S N M) {p : Poly S N} {e a : ℤ} {m : M}
    (hp : p ∈ (polyGraded S N).piece e) (hm : m ∈ 𝓜.piece a) : p • m ∈ 𝓜.piece (a + e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GradedPMod».«smul_mem_int» := P2M_GroundTheory_Heights__Heights_Kleiman_GradedPMod_smul_mem_int_382e083d6e10
