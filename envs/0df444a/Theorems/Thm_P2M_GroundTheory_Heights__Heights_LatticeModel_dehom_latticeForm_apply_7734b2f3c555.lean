-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_apply_7734b2f3c555
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_apply_7734b2f3c555
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:43:14.499103+00:00
-- url     : https://prove2.me/theorems/231dcd47-e234-57eb-9765-000bd8711c43
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form apply 7734b2f3c555: P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form apply 7734b2f3c555
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form apply 7734b2f3c555 construction uses the P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form apply 7734b2f3c555 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L159-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L159-L161

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
variable {r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)} {φ : Fin (N + 1) → Fin (r + 1) → K}

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_apply_7734b2f3c555 (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) = ∑ j, algebraMap K (LatticeField K r) (u j) * genericVal K r j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«dehom_latticeForm_apply» := P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_apply_7734b2f3c555
