-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_sum_776f66a088f8
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_sum_776f66a088f8
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:24.410443+00:00
-- url     : https://prove2.me/theorems/d3996742-72c8-400c-9f15-ef585f21ba77
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model lattice Form sum 776f66a088f8: P2 M Ground Theory Heights  Heights Lattice Model lattice Form sum 776f66a088f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model lattice Form sum 776f66a088f8 construction uses the P2 M Ground Theory Heights  Heights Lattice Model lattice Form sum 776f66a088f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L71-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K]
variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_sum_776f66a088f8 {ι : Type*} (s : Finset ι) (u : ι → Fin m → K) :
    latticeForm (∑ i ∈ s, u i) = ∑ i ∈ s, latticeForm (u i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«latticeForm_sum» := P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_sum_776f66a088f8
