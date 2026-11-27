-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_aeval_latticeCoord_5374d9b57203
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_aeval_latticeCoord_5374d9b57203
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:32:00.812606+00:00
-- url     : https://prove2.me/theorems/0b70a7a6-aa58-589f-81c6-15fae89fec8d
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model aeval lattice Coord 5374d9b57203: P2 M Ground Theory Heights  Heights Lattice Model aeval lattice Coord 5374d9b57203
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model aeval lattice Coord 5374d9b57203 construction uses the P2 M Ground Theory Heights  Heights Lattice Model aeval lattice Coord 5374d9b57203 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L194-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L194-L202

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_aeval_latticeCoord_5374d9b57203 (φ : Fin (N + 1) → Fin (r + 1) → K) (g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) :
    aeval (latticeCoord φ) g = dehom K r (latticeMap φ g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«aeval_latticeCoord» := P2M_GroundTheory_Heights__Heights_LatticeModel_aeval_latticeCoord_5374d9b57203
