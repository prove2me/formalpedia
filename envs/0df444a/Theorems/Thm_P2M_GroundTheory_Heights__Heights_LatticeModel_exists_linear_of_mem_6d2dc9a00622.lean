-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_exists_linear_of_mem_6d2dc9a00622
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_exists_linear_of_mem_6d2dc9a00622
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:40.304146+00:00
-- url     : https://prove2.me/theorems/6fb091a9-e58e-4fd4-8a84-f496f407753b
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model exists linear of mem 6d2dc9a00622: P2 M Ground Theory Heights  Heights Lattice Model exists linear of mem 6d2dc9a00622
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model exists linear of mem 6d2dc9a00622 construction uses the P2 M Ground Theory Heights  Heights Lattice Model exists linear of mem 6d2dc9a00622 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L188-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L188-L193

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
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
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
variable {φ : Fin (N + 1) → Fin m → K}
variable {r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)} {φ : Fin (N + 1) → Fin (r + 1) → K}

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_exists_linear_of_mem_6d2dc9a00622 {m : ℕ} {L' : Submodule (𝓞 K) (Fin m → K)} {φ' : Fin (N + 1) → Fin m → K}
    (hφ : IsDualBasis L' φ') {u : Fin m → K} (hu : u ∈ latticeDual L') :
    ∃ g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ, g.IsHomogeneous 1 ∧ latticeMap φ' g = latticeForm u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«exists_linear_of_mem» := P2M_GroundTheory_Heights__Heights_LatticeModel_exists_linear_of_mem_6d2dc9a00622
