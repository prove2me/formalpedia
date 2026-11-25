-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_prod_mem_latticeMap_image_bdcb5725007a
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_prod_mem_latticeMap_image_bdcb5725007a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:31.068808+00:00
-- url     : https://prove2.me/theorems/c925d777-6c93-4ef2-a881-eb60eba6764b
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model prod mem lattice Map image bdcb5725007a: P2 M Ground Theory Heights  Heights Lattice Model prod mem lattice Map image bdcb5725007a
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model prod mem lattice Map image bdcb5725007a construction uses the P2 M Ground Theory Heights  Heights Lattice Model prod mem lattice Map image bdcb5725007a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L88-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L88-L98

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_prod_mem_latticeMap_image_bdcb5725007a (hφ : IsDualBasis L φ) {d : ℕ} (u : Fin d → Fin m → K)
    (hu : ∀ i, u i ∈ latticeDual L) :
    ∃ f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ, f.IsHomogeneous d ∧ latticeMap φ f = ∏ i, latticeForm (u i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«prod_mem_latticeMap_image» := P2M_GroundTheory_Heights__Heights_LatticeModel_prod_mem_latticeMap_image_bdcb5725007a
