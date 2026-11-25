-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_evalCone_cross_3f7d63056fd1
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_evalCone_cross_3f7d63056fd1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:30.027628+00:00
-- url     : https://prove2.me/theorems/ae03d2f0-857d-55e8-9c7d-91c69dc6c29d
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections eval Cone cross 3f7d63056fd1: P2 M Ground Theory Heights  Heights Small Sections eval Cone cross 3f7d63056fd1
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections eval Cone cross 3f7d63056fd1 construction uses the P2 M Ground Theory Heights  Heights Small Sections eval Cone cross 3f7d63056fd1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L215-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L215-L244

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
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
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_SmallSections_evalCone_cross_3f7d63056fd1 {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0)
    (c' : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)) :
    evalCone z (g c' j) =
      evalCone z (chartMonomial c' d) * evalCone z (g c j) / evalCone z (chartMonomial c d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«evalCone_cross» := P2M_GroundTheory_Heights__Heights_SmallSections_evalCone_cross_3f7d63056fd1
