-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeVariety_ideal_03c5362aa5c6
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_latticeVariety_ideal_03c5362aa5c6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:29:10.771309+00:00
-- url     : https://prove2.me/theorems/c849c1dc-2e70-48a3-b6e4-c5fb72939cb9
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model lattice Variety ideal 03c5362aa5c6: P2 M Ground Theory Heights  Heights Lattice Model lattice Variety ideal 03c5362aa5c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model lattice Variety ideal 03c5362aa5c6 construction uses the P2 M Ground Theory Heights  Heights Lattice Model lattice Variety ideal 03c5362aa5c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L169-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L169-L170

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_latticeVariety_ideal_03c5362aa5c6 (φ : Fin (N + 1) → Fin m → K) (hφ : IsDualBasis L φ) :
    (latticeVariety φ hφ).ideal = latticeIdeal φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«latticeVariety_ideal» := P2M_GroundTheory_Heights__Heights_LatticeModel_latticeVariety_ideal_03c5362aa5c6
