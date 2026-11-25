-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_image_homogeneous_5a8f9f7890e0
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_image_homogeneous_5a8f9f7890e0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:30:50.609493+00:00
-- url     : https://prove2.me/theorems/f66cac10-44ef-4b65-bde9-3bddd9836afb
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model lattice Map image homogeneous 5a8f9f7890e0: P2 M Ground Theory Heights  Heights Lattice Model lattice Map image homogeneous 5a8f9f7890e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model lattice Map image homogeneous 5a8f9f7890e0 construction uses the P2 M Ground Theory Heights  Heights Lattice Model lattice Map image homogeneous 5a8f9f7890e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L100-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L100-L141

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_image_homogeneous_5a8f9f7890e0 (hφ : IsDualBasis L φ) {d : ℕ} (hd : 1 ≤ d) :
    latticeMap φ '' {f | IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ N) f (fun _ ↦ d)} =
      (prodSpan L d : Set (MvPolynomial (Fin m) K)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«latticeMap_image_homogeneous» := P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_image_homogeneous_5a8f9f7890e0
