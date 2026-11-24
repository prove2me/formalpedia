-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_finite_latticePoints_4885546fbfad
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_finite_latticePoints_4885546fbfad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:09.799958+00:00
-- url     : https://prove2.me/theorems/504bbf8e-14f6-472c-9d81-3f52c3b2b5d8
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count finite lattice Points 4885546fbfad: P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count finite lattice Points 4885546f
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count finite lattice Points 4885546fbfad construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count finite lattice Points 4885546fbfad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMinkowskiCount.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMinkowskiCount.lean#L21-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMinkowskiCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Module Metric
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
omit [MeasurableSpace V] [BorelSpace V]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_finite_latticePoints_4885546fbfad (La : Submodule ℤ V) [DiscreteTopology La] (ρ : ℝ) :
    {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MinkowskiCount».«finite_latticePoints» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_finite_latticePoints_4885546fbfad
