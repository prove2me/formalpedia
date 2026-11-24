-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval__scale_of_isWeightedHomogeneous_6a2760d9d5f2
-- name    : P2M_GroundTheory_Heights__Heights_eval__scale_of_isWeightedHomogeneous_6a2760d9d5f2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:24.093414+00:00
-- url     : https://prove2.me/theorems/9bd4a535-03fb-449c-950c-c3802381a178
-- title:
--   P2 M Ground Theory Heights  Heights eval  scale of is Weighted Homogeneous 6a2760d9d5f2: P2 M Ground Theory Heights  Heights eval  scale of is Weighted Homogeneous 6a2760d9d5f2
-- statement:
--   The P2 M Ground Theory Heights  Heights eval  scale of is Weighted Homogeneous 6a2760d9d5f2 construction uses the P2 M Ground Theory Heights  Heights eval  scale of is Weighted Homogeneous 6a2760d9d5f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L15-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L15-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_eval__scale_of_isWeightedHomogeneous_6a2760d9d5f2 {S : Type*} [CommRing S] [Fintype ι] (w : ι → S)
    (x : Coord n → S) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    eval₂ (Int.castRingHom S) (fun v ↦ w v.1 * x v) f =
      (∏ k, w k ^ δ k) * eval₂ (Int.castRingHom S) x f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval₂_scale_of_isWeightedHomogeneous» := P2M_GroundTheory_Heights__Heights_eval__scale_of_isWeightedHomogeneous_6a2760d9d5f2
