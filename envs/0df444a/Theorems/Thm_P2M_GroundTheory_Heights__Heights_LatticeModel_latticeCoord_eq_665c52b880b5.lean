-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_eq_665c52b880b5
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_eq_665c52b880b5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:01.387208+00:00
-- url     : https://prove2.me/theorems/2ecffc61-3be6-4651-a68a-4f14ecdcfbcf
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model lattice Coord eq 665c52b880b5: P2 M Ground Theory Heights  Heights Lattice Model lattice Coord eq 665c52b880b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model lattice Coord eq 665c52b880b5 construction uses the P2 M Ground Theory Heights  Heights Lattice Model lattice Coord eq 665c52b880b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L190-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L190-L192

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_eq_665c52b880b5 (φ : Fin (N + 1) → Fin (r + 1) → K) (v : Coord fun _ : Unit ↦ N) :
    latticeCoord φ v = dehom K r (latticeForm (φ v.2)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«latticeCoord_eq» := P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_eq_665c52b880b5
