-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_isWeightedHomogeneous_coordDeg_iff_c2022d0310d2
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_isWeightedHomogeneous_coordDeg_iff_c2022d0310d2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:22.922158+00:00
-- url     : https://prove2.me/theorems/8a83a12b-1162-4ae7-b45a-cc736964016b
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model is Weighted Homogeneous coord Deg iff c2022d0310d2: P2 M Ground Theory Heights  Heights Lattice Model is Weighted Homogeneous coord Deg iff c2022d0310
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model is Weighted Homogeneous coord Deg iff c2022d0310d2 construction uses the P2 M Ground Theory Heights  Heights Lattice Model is Weighted Homogeneous coord Deg iff c2022d0310d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L118-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L118-L131

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
variable {R : Type*} [CommSemiring R]

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_isWeightedHomogeneous_coordDeg_iff_c2022d0310d2 (f : MvPolynomial (Coord fun _ : Unit ↦ N) R) (μ : Unit → ℕ) :
    IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ N) f μ ↔ f.IsHomogeneous (μ ()) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«isWeightedHomogeneous_coordDeg_iff» := P2M_GroundTheory_Heights__Heights_LatticeModel_isWeightedHomogeneous_coordDeg_iff_c2022d0310d2
