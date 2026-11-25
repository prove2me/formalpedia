-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_mem_9c019e288fdd
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_mem_9c019e288fdd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:41.634408+00:00
-- url     : https://prove2.me/theorems/d179e1c0-a603-4d0e-9128-6db67e8594b0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman free Map mem 9c019e288fdd: P2 M Ground Theory Heights  Heights Kleiman free Map mem 9c019e288fdd
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman free Map mem 9c019e288fdd construction uses the P2 M Ground Theory Heights  Heights Kleiman free Map mem 9c019e288fdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L192-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L192-L199

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
omit [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_mem_9c019e288fdd {r : ℕ} (𝓜 : GradedPMod S N M) {g : Fin r → M} {deg : Fin r → ℤ}
    (hg : ∀ j, g j ∈ 𝓜.piece (deg j)) (c : ℤ) {f : Fin r → Poly S N}
    (hf : f ∈ (freeGraded S N deg).piece c) : freeMap S N g f ∈ 𝓜.piece c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«freeMap_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_mem_9c019e288fdd
