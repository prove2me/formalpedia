-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_joinPt_mem_extPoints_65b19b23e102
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_joinPt_mem_extPoints_65b19b23e102
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:08.633611+00:00
-- url     : https://prove2.me/theorems/17e79659-3b51-4426-897c-6611b78724ba
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections join Pt mem ext Points 65b19b23e102: P2 M Ground Theory Heights  Heights Small Sections join Pt mem ext Points 65b19b23e102
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections join Pt mem ext Points 65b19b23e102 construction uses the P2 M Ground Theory Heights  Heights Small Sections join Pt mem ext Points 65b19b23e102 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L194-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L194-L213

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

theorem P2M_GroundTheory_Heights__Heights_SmallSections_joinPt_mem_extPoints_65b19b23e102 {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0) :
    D.joinPt z (fun j ↦ evalCone z (g c j)) ∈ D.extPoints := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«joinPt_mem_extPoints» := P2M_GroundTheory_Heights__Heights_SmallSections_joinPt_mem_extPoints_65b19b23e102
