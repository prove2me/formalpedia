-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_ne_zero_0edf84f2cbfa
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_ne_zero_0edf84f2cbfa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:37.238624+00:00
-- url     : https://prove2.me/theorems/5e45cef8-a90a-41bc-ae83-ba8437560113
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model lattice Coord ne zero 0edf84f2cbfa: P2 M Ground Theory Heights  Heights Lattice Model lattice Coord ne zero 0edf84f2cbfa
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model lattice Coord ne zero 0edf84f2cbfa construction uses the P2 M Ground Theory Heights  Heights Lattice Model lattice Coord ne zero 0edf84f2cbfa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModel.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModel.lean#L30-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModel
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
variable {K : Type} [Field K] [NumberField K] {N r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)}
  {φ : Fin (N + 1) → Fin (r + 1) → K}

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_ne_zero_0edf84f2cbfa (hφ : IsDualBasis L φ) (b : Fin (N + 1)) : latticeCoord φ ⟨(), b⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«latticeCoord_ne_zero» := P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_ne_zero_0edf84f2cbfa
