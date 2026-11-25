-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_add_ff76c8df2829
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_add_ff76c8df2829
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:34:08.277796+00:00
-- url     : https://prove2.me/theorems/3c02de0c-0a51-4a9a-b09b-bca7326ca26f
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model lattice Form add ff76c8df2829: P2 M Ground Theory Heights  Heights Lattice Model lattice Form add ff76c8df2829
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model lattice Form add ff76c8df2829 construction uses the P2 M Ground Theory Heights  Heights Lattice Model lattice Form add ff76c8df2829 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L56-L57

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_add_ff76c8df2829 (u v : Fin m → K) : latticeForm (u + v) = latticeForm u + latticeForm v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«latticeForm_add» := P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_add_ff76c8df2829
