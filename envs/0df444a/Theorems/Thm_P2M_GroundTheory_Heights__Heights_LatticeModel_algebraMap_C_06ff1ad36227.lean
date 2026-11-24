-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_algebraMap_C_06ff1ad36227
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_algebraMap_C_06ff1ad36227
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:00.768344+00:00
-- url     : https://prove2.me/theorems/1ea84ef6-799d-44a0-af09-b1d7dc705817
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model algebra Map C 06ff1ad36227: P2 M Ground Theory Heights  Heights Lattice Model algebra Map C 06ff1ad36227
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model algebra Map C 06ff1ad36227 construction uses the P2 M Ground Theory Heights  Heights Lattice Model algebra Map C 06ff1ad36227 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L174-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L174-L176

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_algebraMap_C_06ff1ad36227 (a : K) :
    algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (C a) = algebraMap K (LatticeField K r) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«algebraMap_C» := P2M_GroundTheory_Heights__Heights_LatticeModel_algebraMap_C_06ff1ad36227
