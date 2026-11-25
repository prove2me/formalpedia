-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_surjective_0efadb208268
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_surjective_0efadb208268
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:27.089368+00:00
-- url     : https://prove2.me/theorems/e497adcc-0678-4b8b-8a8e-96ed961968f7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman free Map surjective 0efadb208268: P2 M Ground Theory Heights  Heights Kleiman free Map surjective 0efadb208268
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman free Map surjective 0efadb208268 construction uses the P2 M Ground Theory Heights  Heights Kleiman free Map surjective 0efadb208268 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L202-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L202-L209

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
omit [Module S M] [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_surjective_0efadb208268 {r : ℕ} {g : Fin r → M} (hg : Submodule.span (Poly S N) (Set.range g) = ⊤) :
    Function.Surjective (freeMap S N g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«freeMap_surjective» := P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_surjective_0efadb208268
