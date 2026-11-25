-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sum_locMap_basis_bd6d991ae90c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_sum_locMap_basis_bd6d991ae90c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:30:50.316097+00:00
-- url     : https://prove2.me/theorems/6edd0c76-6e6a-4e5e-b9b4-aa86dadc17bf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman sum loc Map basis bd6d991ae90c: P2 M Ground Theory Heights  Heights Kleiman sum loc Map basis bd6d991ae90c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman sum loc Map basis bd6d991ae90c construction uses the P2 M Ground Theory Heights  Heights Kleiman sum loc Map basis bd6d991ae90c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreFree.lean#L124-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreFree.lean#L124-L147

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFree
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
universe u v w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
variable (𝓜 : GradedPMod S N M) {r : ℕ} (b : Module.Basis (Fin r) (Poly S N) M) (d : Fin r → ℤ)
omit [Module S M] [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_sum_locMap_basis_bd6d991ae90c (I : Finset (Fin (N + 1))) (y : LocMod S N M I) :
    ∑ j, locMap (LinearMap.toSpanSingleton (Poly S N) M (b j)) I (locMap (b.coord j) I y) = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«sum_locMap_basis» := P2M_GroundTheory_Heights__Heights_Kleiman_sum_locMap_basis_bd6d991ae90c
