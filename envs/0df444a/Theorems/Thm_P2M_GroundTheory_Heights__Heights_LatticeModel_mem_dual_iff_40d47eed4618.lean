-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_mem_dual_iff_40d47eed4618
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_mem_dual_iff_40d47eed4618
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:56.840173+00:00
-- url     : https://prove2.me/theorems/40489a97-c75a-49f5-82c4-fcb6f5dd2816
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model mem dual iff 40d47eed4618: P2 M Ground Theory Heights  Heights Lattice Model mem dual iff 40d47eed4618
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model mem dual iff 40d47eed4618 construction uses the P2 M Ground Theory Heights  Heights Lattice Model mem dual iff 40d47eed4618 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L49-L51

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_mem_dual_iff_40d47eed4618 (hφ : IsDualBasis L φ) (u : Fin m → K) :
    u ∈ latticeDual L ↔ ∃ c : Fin (N + 1) → ℤ, ∑ b, c b • φ b = u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«mem_dual_iff» := P2M_GroundTheory_Heights__Heights_LatticeModel_mem_dual_iff_40d47eed4618
