-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_linear_b60498b1849d
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_linear_b60498b1849d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:14.517092+00:00
-- url     : https://prove2.me/theorems/31d846d3-150f-4980-a310-4e22f693d31b
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model lattice Map linear b60498b1849d: P2 M Ground Theory Heights  Heights Lattice Model lattice Map linear b60498b1849d
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model lattice Map linear b60498b1849d construction uses the P2 M Ground Theory Heights  Heights Lattice Model lattice Map linear b60498b1849d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L89-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L89-L94

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_linear_b60498b1849d (φ : Fin (N + 1) → Fin m → K) (c : Fin (N + 1) → ℤ) :
    latticeMap φ (∑ b, C (c b) * X ⟨(), b⟩) = latticeForm (∑ b, c b • φ b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«latticeMap_linear» := P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_linear_b60498b1849d
