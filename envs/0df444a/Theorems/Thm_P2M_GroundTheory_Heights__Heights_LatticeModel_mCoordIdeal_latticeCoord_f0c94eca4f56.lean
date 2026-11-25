-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_mCoordIdeal_latticeCoord_f0c94eca4f56
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_mCoordIdeal_latticeCoord_f0c94eca4f56
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:37:37.750617+00:00
-- url     : https://prove2.me/theorems/b86ee854-ab20-592f-bf10-e2af5bc4b05d
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model m Coord Ideal lattice Coord f0c94eca4f56: P2 M Ground Theory Heights  Heights Lattice Model m Coord Ideal lattice Coord f0c94eca4f56
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model m Coord Ideal lattice Coord f0c94eca4f56 construction uses the P2 M Ground Theory Heights  Heights Lattice Model m Coord Ideal lattice Coord f0c94eca4f56 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L204-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L204-L271

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
variable {r : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_mCoordIdeal_latticeCoord_f0c94eca4f56 (φ : Fin (N + 1) → Fin (r + 1) → K) :
    Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) = latticeIdeal φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«mCoordIdeal_latticeCoord» := P2M_GroundTheory_Heights__Heights_LatticeModel_mCoordIdeal_latticeCoord_f0c94eca4f56
