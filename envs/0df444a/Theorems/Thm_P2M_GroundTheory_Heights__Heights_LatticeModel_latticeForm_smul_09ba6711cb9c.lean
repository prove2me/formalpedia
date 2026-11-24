-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_smul_09ba6711cb9c
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_smul_09ba6711cb9c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:11.944136+00:00
-- url     : https://prove2.me/theorems/c65f7e3b-877b-45be-a84f-557d4896d57d
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model lattice Form smul 09ba6711cb9c: P2 M Ground Theory Heights  Heights Lattice Model lattice Form smul 09ba6711cb9c
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model lattice Form smul 09ba6711cb9c construction uses the P2 M Ground Theory Heights  Heights Lattice Model lattice Form smul 09ba6711cb9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L59-L60

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_smul_09ba6711cb9c (c : K) (u : Fin m → K) : latticeForm (c • u) = C c * latticeForm u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«latticeForm_smul» := P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_smul_09ba6711cb9c
