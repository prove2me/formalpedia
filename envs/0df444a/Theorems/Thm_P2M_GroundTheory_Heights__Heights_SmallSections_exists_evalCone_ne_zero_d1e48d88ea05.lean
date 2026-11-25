-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_exists_evalCone_ne_zero_d1e48d88ea05
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_exists_evalCone_ne_zero_d1e48d88ea05
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:10.681333+00:00
-- url     : https://prove2.me/theorems/7e7b3280-6f4b-4d13-968a-8f47df542588
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections exists eval Cone ne zero d1e48d88ea05: P2 M Ground Theory Heights  Heights Small Sections exists eval Cone ne zero d1e48d88ea05
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections exists eval Cone ne zero d1e48d88ea05 construction uses the P2 M Ground Theory Heights  Heights Small Sections exists eval Cone ne zero d1e48d88ea05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L119-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L119-L166

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

theorem P2M_GroundTheory_Heights__Heights_SmallSections_exists_evalCone_ne_zero_d1e48d88ea05 {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0) :
    ∃ j, evalCone z (g c j) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«exists_evalCone_ne_zero» := P2M_GroundTheory_Heights__Heights_SmallSections_exists_evalCone_ne_zero_d1e48d88ea05
